(*  Title:       Preliminaries_RTS
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

theory Preliminaries
imports Main "HOL-Library.FuncSet"
        ResiduatedTransitionSystem.ResiduatedTransitionSystem
begin

  lemma (in extensional_rts) divisors_of_ide:
  assumes "composite_of t u v" and "ide v"
  shows "ide t" and "ide u"
  proof -
    show "ide t"
      using assms ide_backward_stable by blast
    show "ide u"
      by (metis assms(1-2) composite_ofE con_ide_are_eq con_prfx_composite_of(1)
          ide_backward_stable)
  qed

section "Simulations"

  abbreviation I
  where "I \<equiv> identity_simulation.map"

  lemma comp_identity_simulation:
  assumes "simulation A B F"
  shows "I B \<circ> F = F"
    using assms simulation.extensional simulation.preserves_reflects_arr
    by fastforce

  lemma comp_simulation_identity:
  assumes "simulation A B F"
  shows "F \<circ> I A = F"
    using assms residuation.not_arr_null rts.axioms(1) simulation.extensional
      simulation_def
    by fastforce

  lemma product_identity_simulation:
  assumes "rts A" and "rts B"
  shows "product_simulation.map A B (I A) (I B) = I (product_rts.resid A B)"
  proof -
    interpret A: rts A
      using assms(1) by blast
    interpret B: rts B
      using assms(2) by blast
    interpret A: identity_simulation A ..
    interpret B: identity_simulation B ..
    interpret AxB: product_rts A B ..
    interpret IAxIB: product_simulation A B A B A.map B.map ..
    interpret AxB: identity_simulation AxB.resid ..
    show "IAxIB.map = AxB.map"
      using IAxIB.map_def by auto
  qed

  locale constant_simulation =
    A: rts A +
    B: rts B
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and b :: 'b +
  assumes ide_b: "B.ide b"
  begin

    abbreviation map
    where "map t \<equiv> if A.arr t then b else B.null"

    sublocale simulation A B map
      using ide_b A.con_implies_arr
      by unfold_locales auto

  end

  (*
   * TODO: The order of arguments was defined here to match inverse_functors,
   * which was in turn chosen to match adjunction, but it is very confusing.
   *)
  locale inverse_simulations =
    A: rts A +
    B: rts B +
    F: simulation B A F +
    G: simulation A B G
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and F :: "'b \<Rightarrow> 'a"
  and G :: "'a \<Rightarrow> 'b" +
  assumes inv: "G o F = I B"
  and inv': "F o G = I A"
  begin

    lemma inv_simp [simp]:
    assumes "B.arr y"
    shows "G (F y) = y"
      using assms inv by (metis comp_apply)

    lemma inv'_simp [simp]:
    assumes "A.arr x"
    shows "F (G x) = x"
      using assms inv' by (metis comp_apply)

    lemma induce_bij_betw_arr_sets:
    shows "bij_betw F (Collect B.arr) (Collect A.arr)"
      using inv inv' by (intro bij_betwI) auto

  end

  lemma inverse_simulations_sym:
  assumes "inverse_simulations A B F G"
  shows "inverse_simulations B A G F"
    using assms
    by (simp add: inverse_simulations_axioms_def inverse_simulations_def)

  (* TODO: Interchange the definition and lemma here.  Also improve ordering of stuff. *)
  locale invertible_simulation =
    simulation +
  assumes invertible: "\<exists>G. inverse_simulations A B G F"

  lemma invertible_simulation_def':
  shows "invertible_simulation A B F \<longleftrightarrow> (\<exists>G. inverse_simulations A B G F)"
    using inverse_simulations_def invertible_simulation_axioms_def
          invertible_simulation_def
    by blast

  lemma invertible_simulation_iff:
  shows "invertible_simulation A B F \<longleftrightarrow>
         simulation A B F \<and>
         bij_betw F (Collect (residuation.arr A)) (Collect (residuation.arr B)) \<and>
         (\<forall>t u. residuation.con B (F t) (F u) \<longrightarrow> residuation.con A t u)"
  proof (intro iffI conjI)
    assume F: "invertible_simulation A B F"
    interpret F: invertible_simulation A B F
      using F by blast
    obtain G where G: "inverse_simulations A B G F"
      using F.invertible by blast
    interpret FG: inverse_simulations A B G F
      using G by blast
    show "simulation A B F"
      using F.simulation_axioms by blast
    have *: "\<And>y. y \<in> Collect F.B.arr \<Longrightarrow> F (G y) = y"
      by (metis CollectD FG.inv comp_apply)
    show "bij_betw F (Collect F.A.arr) (Collect F.B.arr)"
      using G inverse_simulations.induce_bij_betw_arr_sets inverse_simulations_sym
      by blast
    show "\<forall>t u. F.B.con (F t) (F u) \<longrightarrow> F.A.con t u"
      by (metis F.B.not_con_null(1) F.B.not_con_null(2) F.extensional FG.F.preserves_con
          FG.inv' comp_apply)
    next
    assume F: "simulation A B F \<and>
               bij_betw F (Collect (residuation.arr A)) (Collect (residuation.arr B)) \<and>
               (\<forall>t u. residuation.con B (F t) (F u) \<longrightarrow> residuation.con A t u)"
    interpret F: simulation A B F
      using F by blast
    let ?G = "\<lambda>y. if y \<in> F ` Collect F.A.arr
                  then inv_into (Collect F.A.arr) F y
                  else F.A.null"
    interpret G: simulation B A ?G
    proof
      show "\<And>t. \<not> F.B.arr t \<Longrightarrow> ?G t = F.A.null"
        by fastforce
      fix t u
      assume 1: "F.B.con t u"
      have 2: "?G t = inv_into (Collect F.A.arr) F t \<and>
               ?G u = inv_into (Collect F.A.arr) F u"
        using 1 F F.B.con_implies_arr
        by (simp add: bij_betw_def)
      have 3: "F.A.con (inv_into (Collect F.A.arr) F t)
                       (inv_into (Collect F.A.arr) F u)"
        using 1 F.B.con_implies_arr F
        by (metis bij_betw_imp_surj_on f_inv_into_f mem_Collect_eq)
      thus 4: "F.A.con (?G t) (?G u)"
        using 2 by simp
      have "?G (B t u) = inv_into (Collect F.A.arr) F (B t u)"
        by (metis 1 F CollectI F.B.arr_resid_iff_con bij_betw_def)
      also have "... = A (?G t) (?G u)"
      proof -
        have "F (A (?G t) (?G u)) = B (F (?G t)) (F (?G u))"
          using 4 F.preserves_resid by presburger
        also have "... = B t u"
          using 4 F.A.not_con_null(1-2) f_inv_into_f
          by (auto simp add: f_inv_into_f)
        finally have "F (A (?G t) (?G u)) = B t u" by blast
        thus ?thesis
          by (metis 4 F F.A.arr_resid bij_betw_inv_into_left mem_Collect_eq)
      qed
      finally show "?G (B t u) = A (?G t) (?G u)" by blast
    qed
    interpret FG: inverse_simulations A B ?G F
    proof
      show "F \<circ> ?G = I B"
      proof
        fix t
        show "(F \<circ> ?G) t = I B t"
          apply simp
          by (metis F F.A.not_arr_null bij_betw_def f_inv_into_f mem_Collect_eq
              simulation.extensional)
      qed
      show "?G \<circ> F = I A"
      proof
        fix t
        show "(?G \<circ> F) t = I A t"
          apply simp
          by (metis F F.preserves_reflects_arr bij_betw_def inv_into_f_f mem_Collect_eq)
      qed
    qed
    show "invertible_simulation A B F"
      using FG.inverse_simulations_axioms invertible_simulation_def
      by unfold_locales blast
  qed

  context invertible_simulation
  begin

    lemma is_bijection_betw_arr_sets:
    shows "bij_betw F (Collect A.arr) (Collect B.arr)"
      using invertible_simulation_axioms invertible_simulation_iff by metis

    lemma reflects_con:
    assumes "residuation.con B (F t) (F u)"
    shows "residuation.con A t u"
      using assms invertible_simulation_axioms invertible_simulation_iff by metis

  end

  context inverse_simulations
  begin

    sublocale F: invertible_simulation B A F
      by (meson inverse_simulations_axioms inverse_simulations_sym invertible_simulation_def')

    sublocale G: invertible_simulation A B G
      by (meson inverse_simulations_axioms invertible_simulation_def')

  end

  lemma inverse_simulation_unique:
  assumes "inverse_simulations A B G F"
  and "inverse_simulations A B G' F"
  shows "G = G'"
  proof -
    interpret FG: inverse_simulations A B G F
      using assms(1) by simp
    interpret FG': inverse_simulations A B G' F
      using assms(2) by simp
    show ?thesis
    proof
      fix x
      show "G x = G' x"
        by (metis FG'.F.extensional FG'.F.preserves_reflects_arr FG'.inv FG.F.extensional
            FG.inv' comp_apply)
    qed
  qed

  locale inverse_simulation =
    A: rts A +
    B: rts B +
    F: invertible_simulation
  begin

    definition map
    where "map \<equiv> SOME G. inverse_simulations A B G F"

    interpretation inverse_simulations A B map F
      using F.invertible invertible_simulation_def map_def
            someI_ex [of "\<lambda>G. inverse_simulations A B G F"]
      by auto

    sublocale simulation B A map ..

    lemma is_simulation:
    shows "simulation B A map"
      ..

    sublocale inverse_simulations A B map F ..

    lemma map_simp:
    assumes "B.arr x"
    shows "map x = inv_into (Collect A.arr) F x"
      by (metis CollectI F.preserves_reflects_arr assms bij_betw_inv_into_left
          inv_simp inverse_simulations.induce_bij_betw_arr_sets
          inverse_simulations_axioms inverse_simulations_sym)

    lemma map_eq:
    shows "map = (\<lambda>x. if B.arr x then inv_into (Collect A.arr) F x else A.null)"
      using map_simp by (meson F.extensional)

  end

  lemma invertible_simulation_identity:
  assumes "rts A"
  shows [intro]: "invertible_simulation A A (I A)"
  and "inverse_simulations A A (I A) (I A)"
  and "inverse_simulation.map A A (I A) = I A"
  proof -
    interpret A: rts A
      using assms by blast
    interpret id: identity_simulation A ..
    show 1: "inverse_simulations A A id.map id.map"
      by unfold_locales auto
    thus "invertible_simulation A A id.map"
      using id.simulation_axioms invertible_simulation.intro
            invertible_simulation_axioms.intro
      by blast
    show "inverse_simulation.map A A id.map = id.map"
      using 1 inverse_simulation_unique [of A A id.map id.map]
      by (metis (no_types, lifting) \<open>invertible_simulation A A id.map\<close> assms
          inverse_simulation.intro inverse_simulation.map_def someI_ex)
  qed

  lemma inverse_simulations_compose:
  assumes "inverse_simulations A B F' F" and "inverse_simulations B C G' G"
  shows "inverse_simulations A C (F' \<circ> G') (G \<circ> F)"
  proof -
    interpret FF': inverse_simulations A B F' F
      using assms by blast
    interpret GG': inverse_simulations B C G' G
      using assms by blast
    interpret GoF: composite_simulation A B C F G ..
    interpret F'oG': composite_simulation C B A G' F' ..
    show ?thesis
    proof
      show "GoF.map \<circ> F'oG'.map = I C"
        by (metis FF'.inv GG'.F.extensional GG'.F.preserves_reflects_arr
            GG'.inv comp_def)
      show "F'oG'.map \<circ> GoF.map = I A"
        by (metis FF'.A.not_arr_null FF'.G.preserves_reflects_arr FF'.inv
            FF'.inv' GG'.inv' comp_apply)
    qed
  qed

  lemma invertible_simulation_comp [intro]:
  assumes "invertible_simulation A B F" and "invertible_simulation B C G"
  shows "invertible_simulation A C (G \<circ> F)"
  and "inverse_simulations A C
         (inverse_simulation.map A B F \<circ> inverse_simulation.map B C G) (G \<circ> F)"
  and "inverse_simulation.map A C (G \<circ> F) =
       inverse_simulation.map A B F \<circ> inverse_simulation.map B C G"
  proof -
    obtain F' where F': "inverse_simulations A B F' F"
      using assms(1) invertible_simulation.invertible by blast
    interpret FF': inverse_simulations A B F' F
      using F' by blast
    obtain G' where G': "inverse_simulations B C G' G"
      using assms(2) invertible_simulation.invertible by blast
    interpret GG': inverse_simulations B C G' G
      using G' by blast
    interpret GoF: composite_simulation A B C F G ..
    interpret F'oG': composite_simulation C B A G' F' ..
    interpret F': inverse_simulation A B F
      using F' assms(1) inverse_simulation_def inverse_simulations_def by blast
    interpret G': inverse_simulation B C G
      using G' assms(2)
      by (simp add: inverse_simulation.intro inverse_simulations_def)
    have F'_eq: "F' = F'.map"
      using F' F'.inverse_simulations_axioms inverse_simulation_unique by blast
    have G'_eq: "G' = G'.map"
      using G' G'.inverse_simulations_axioms inverse_simulation_unique by blast
    have 1: "inverse_simulations A C (F' \<circ> G') (G \<circ> F)"
      using F' G' inverse_simulations_compose by blast
    thus 2: "invertible_simulation A C (G \<circ> F)"
      using invertible_simulation_def by unfold_locales blast
    show "inverse_simulations A C (F'.map \<circ> G'.map) GoF.map"
      using F'_eq G'_eq 1 by blast
    show "inverse_simulation.map A C GoF.map = F'.map \<circ> G'.map"
      using 1 2 F'_eq G'_eq inverse_simulation_unique
      by (metis FF'.A.rts_axioms GG'.B.rts_axioms inverse_simulation.intro
          inverse_simulation.map_def someI_ex)
  qed

  lemma inverse_simulation_product [intro]:
  assumes "invertible_simulation A B F" and "invertible_simulation C D G"
  shows "invertible_simulation (product_rts.resid A C) (product_rts.resid B D)
           (product_simulation.map A C F G)"
  and "inverse_simulations (product_rts.resid A C) (product_rts.resid B D)
         (product_simulation.map B D
            (inverse_simulation.map A B F) (inverse_simulation.map C D G))
         (product_simulation.map A C F G)"
  and "inverse_simulation.map (product_rts.resid A C) (product_rts.resid B D)
         (product_simulation.map A C F G) =
       product_simulation.map B D
         (inverse_simulation.map A B F) (inverse_simulation.map C D G)"
  proof -
    interpret A: rts A
      using assms(1) by (simp add: invertible_simulation_iff simulation_def)
    interpret B: rts B
      using assms(1) by (simp add: invertible_simulation_iff simulation_def)
    interpret C: rts C
      using assms(2) by (simp add: invertible_simulation_iff simulation_def)
    interpret D: rts D
      using assms(2) by (simp add: invertible_simulation_iff simulation_def)
    interpret AxC: product_rts A C ..
    interpret BxD: product_rts B D ..
    interpret F: simulation A B F
      using assms(1) invertible_simulation_def invertible_simulation_iff by blast
    interpret F': inverse_simulation A B F
      using assms(1) invertible_simulation.invertible by unfold_locales auto
    interpret FF': inverse_simulations A B F'.map F ..
    interpret G: simulation C D G
      using assms(2) invertible_simulation_def invertible_simulation_iff by blast
    interpret G': inverse_simulation C D G
      using assms(2) invertible_simulation.invertible by unfold_locales auto
    interpret GG': inverse_simulations C D G'.map G ..
    interpret FxG: product_simulation A C B D F G ..
    interpret F'xG': product_simulation B D A C F'.map G'.map ..
    interpret inverse_simulations AxC.resid BxD.resid F'xG'.map FxG.map
    proof
      show "FxG.map \<circ> F'xG'.map = I BxD.resid"
      proof
        fix t
        show "(FxG.map \<circ> F'xG'.map) t = I BxD.resid t"
          using F'.inv G'.inv FxG.map_def F'xG'.map_def
                F.extensional G.extensional
          by auto
      qed
      show "F'xG'.map \<circ> FxG.map = I AxC.resid"
      proof
        fix t
        show "(F'xG'.map \<circ> FxG.map) t = I AxC.resid t"
          using F'.inv' G'.inv' FxG.map_def F'xG'.map_def
                F'.extensional G'.extensional
          by auto
      qed
    qed
    show "inverse_simulations AxC.resid BxD.resid F'xG'.map FxG.map" ..
    show "invertible_simulation AxC.resid BxD.resid FxG.map"
      using inverse_simulations_axioms
      by unfold_locales blast
    thus "inverse_simulation.map AxC.resid BxD.resid FxG.map = F'xG'.map"
      by (metis inverse_simulation.intro inverse_simulation.map_def
          inverse_simulation_unique inverse_simulations_axioms invertible_simulation_def
          simulation_def someI_ex)
  qed

  lemma invertible_simulation_cancel_left:
  assumes "invertible_simulation A B H"
  shows "\<lbrakk>simulation C A F; simulation C A G; H \<circ> F = H \<circ> G\<rbrakk> \<Longrightarrow> F = G"
  proof -
    obtain K where K: "inverse_simulations A B K H"
      using assms(1) invertible_simulation.invertible by blast
    interpret HK: inverse_simulations A B K H
      using K by blast
    show "\<lbrakk>simulation C A F; simulation C A G; H \<circ> F = H \<circ> G\<rbrakk> \<Longrightarrow> F = G"
      by (metis HK.inv' HOL.ext comp_def simulation.extensional
          simulation.preserves_reflects_arr)
  qed

  lemma invertible_simulation_cancel_right:
  assumes "invertible_simulation A B H"
  shows "\<lbrakk>simulation B C F; simulation B C G; F \<circ> H = G \<circ> H\<rbrakk> \<Longrightarrow> F = G"
  proof -
    obtain K where K: "inverse_simulations A B K H"
      using assms(1) invertible_simulation.invertible by blast
    interpret HK: inverse_simulations A B K H
      using K by blast
    show "\<lbrakk>simulation B C F; simulation B C G; F \<circ> H = G \<circ> H\<rbrakk> \<Longrightarrow> F = G"
      by (metis HK.inv HOL.ext comp_def simulation.extensional)
  qed

  definition isomorphic_rts
  where "isomorphic_rts A B \<equiv> \<exists>F G. inverse_simulations A B G F"

  lemma isomorphic_rts_reflexive:
  assumes "rts A"
  shows "isomorphic_rts A A"
    using assms invertible_simulation_identity isomorphic_rts_def by blast

  lemma isomorphic_rts_symmetric:
  assumes "isomorphic_rts A B"
  shows "isomorphic_rts B A"
    using assms inverse_simulations_sym isomorphic_rts_def by meson

  lemma isomorphic_rts_transitive [trans]:
  assumes "isomorphic_rts A B" and "isomorphic_rts B C"
  shows "isomorphic_rts A C"
    using assms invertible_simulation_comp(1) isomorphic_rts_def
          invertible_simulation_def
    by (metis inverse_simulations.axioms(4) invertible_simulation.invertible
        invertible_simulation_axioms.intro)

  lemma (in simulation) simulation_inv_intoI:
  assumes "inj_on F (Collect A.arr)" and "F ` (Collect A.arr) = Collect B.arr"
  and "\<And>t. \<not> B.arr t \<Longrightarrow> inv_into (Collect A.arr) F t = A.null"
  and "\<And>t u. t \<frown>\<^sub>B u \<Longrightarrow>
               inv_into (Collect A.arr) F t \<frown>\<^sub>A inv_into (Collect A.arr) F u"
  shows "simulation B A (inv_into (Collect A.arr) F)"
  proof
    show "\<And>t. \<not> B.arr t \<Longrightarrow> inv_into (Collect A.arr) F t = A.null"
      using assms(3) by blast
    show "\<And>t u. t \<frown>\<^sub>B u \<Longrightarrow>
                   inv_into (Collect A.arr) F t \<frown>\<^sub>A inv_into (Collect A.arr) F u"
      using assms(4) by blast
    show "\<And>t u. t \<frown>\<^sub>B u \<Longrightarrow>
                   inv_into (Collect A.arr) F (t \\\<^sub>B u) =
                   inv_into (Collect A.arr) F t \\\<^sub>A inv_into (Collect A.arr) F u"
      by (simp add: assms(1-2,4) f_inv_into_f inv_into_f_eq B.con_implies_arr(1-2))
  qed

section "Transformations"

  lemma (in transformation) preserves_arr:
  assumes "A.arr t"
  shows "B.arr (\<tau> t)"
    using assms B.join_of_un_upto_cong B.prfx_implies_con naturality3 by blast

  lemma (in transformation) preserves_con:
  assumes "t \<frown>\<^sub>A u"
  shows "\<tau> t \<frown>\<^sub>B \<tau> u" and "\<tau> t \<frown>\<^sub>B F u"
  proof -
    show "\<tau> t \<frown>\<^sub>B \<tau> u"
    proof (intro B.con_with_join_of_iff(1))
      show "B.join_of (\<tau> (A.src t)) (F t) (\<tau> t)"
        using assms naturality3 [of t] A.con_implies_arr(1) by blast
      show "F t \<frown>\<^sub>B \<tau> u \<and> \<tau> u \\\<^sub>B F t \<frown>\<^sub>B \<tau> (A.src t) \\\<^sub>B F t"
      proof (intro conjI)
        show "\<tau> u \\\<^sub>B F t \<frown>\<^sub>B \<tau> (A.src t) \\\<^sub>B F t"
        proof -
          have "(\<tau> u \\\<^sub>B F t \<frown>\<^sub>B \<tau> (A.src t) \\\<^sub>B F t) \<longleftrightarrow>
                (\<tau> u \\\<^sub>B \<tau> (A.src t) \<frown>\<^sub>B F t \\\<^sub>B \<tau> (A.src t))"
            using B.con_def B.cube by force
          also have "... \<longleftrightarrow> \<tau> u \\\<^sub>B \<tau> (A.src t) \<frown>\<^sub>B G t"
            using A.con_implies_arr(1) assms naturality2 by force
          also have "... \<longleftrightarrow> G u \<frown>\<^sub>B G t"
            by (metis (mono_tags, lifting) A.con_imp_eq_src A.con_implies_arr(2)
                B.composite_ofE B.cong_subst_left(1) B.join_ofE assms
                naturality2 naturality3)
          also have "... = True"
            using assms A.con_sym G.preserves_con by blast
          finally show ?thesis by blast
        qed
        thus "F t \<frown>\<^sub>B \<tau> u"
          by (metis B.con_def B.con_sym B.not_con_null(1))
      qed
    qed
    thus "\<tau> t \<frown>\<^sub>B F u"
      using assms
      by (meson A.residuation_axioms B.con_sym B.con_with_join_of_iff(2)
          B.join_of_symmetric naturality3 residuation.con_implies_arr(2))
  qed

  lemma (in transformation) naturality1':
  assumes "A.arr t"
  shows "B.composite_of (F t) (\<tau> (A.trg t)) (\<tau> t)"
    using assms
    by (metis B.rts_axioms naturality1 naturality3 rts.join_ofE)

  lemma (in transformation) naturality2':
  assumes "A.arr t"
  shows "B.composite_of (\<tau> (A.src t)) (G t) (\<tau> t)"
      by (metis B.join_ofE assms naturality2 naturality3)

  locale transformation_to_extensional_rts =
    transformation +
    B: extensional_rts B
  begin

    notation B.comp  (infixr "\<cdot>\<^sub>B" 55)
    notation B.join  (infix "\<squnion>\<^sub>B" 52)

    lemma naturality1'\<^sub>E:
    shows "F t \<cdot>\<^sub>B \<tau> (A.trg t) = \<tau> t"
    and "A.arr t \<Longrightarrow> B.composable (F t) (\<tau> (A.trg t))"
    proof -
      show "F t \<cdot>\<^sub>B \<tau> (A.trg t) = \<tau> t"
        using naturality1' B.comp_is_composite_of(2)
        by (metis A.arr_trg_iff_arr B.comp_null(2) extensional)
      thus "A.arr t \<Longrightarrow> B.composable (F t) (\<tau> (A.trg t))"
        by (simp add: B.composable_iff_arr_comp preserves_arr)
    qed

    lemma naturality2'\<^sub>E:
    shows "\<tau> (A.src t) \<cdot>\<^sub>B G t = \<tau> t"
    and "A.arr t \<Longrightarrow> B.composable (\<tau> (A.src t)) (G t)"
    proof -
      show "\<tau> (A.src t) \<cdot>\<^sub>B G t = \<tau> t"
        using naturality2' B.comp_is_composite_of(2)
        by (metis B.comp_null(2) G.extensional extensional)
      thus "A.arr t \<Longrightarrow> B.composable (\<tau> (A.src t)) (G t)"
        by (simp add: B.composable_iff_arr_comp preserves_arr)
    qed

    lemma naturality3'\<^sub>E:
    shows "\<tau> (A.src t) \<squnion>\<^sub>B F t = \<tau> t"
    and "A.arr t \<Longrightarrow> B.joinable (\<tau> (A.src t)) (F t)"
    proof -
      show "\<tau> (A.src t) \<squnion>\<^sub>B F t = \<tau> t"
        using naturality3
        by (metis A.not_arr_null A.src_def B.join_def B.join_is_join_of
            B.join_of_unique B.joinable_def B.joinable_implies_con
            B.not_arr_null F.extensional extensional B.arrI)
      thus "A.arr t \<Longrightarrow> B.joinable (\<tau> (A.src t)) (F t)"
        by (metis B.joinable_iff_arr_join preserves_arr)
    qed

    lemma naturality\<^sub>E:
    shows "\<tau> (A.src t) \<cdot>\<^sub>B G t = F t \<cdot>\<^sub>B \<tau> (A.trg t)"
      using naturality1'\<^sub>E(1) naturality2'\<^sub>E(1) by presburger

    lemma general_naturality:
    assumes "A.con x y"
    shows "\<tau> x \\\<^sub>B F y = \<tau> (x \\\<^sub>A y)"
    and "F x \\\<^sub>B \<tau> y = G (x \\\<^sub>A y)"
    proof -
      show "\<tau> x \\\<^sub>B F y = \<tau> (x \\\<^sub>A y)"
        using assms
        by (metis (full_types) A.residuation_axioms A.weakly_extensional_rts_axioms
            B.extensional_rts_axioms G.simulation_axioms extensional_rts.resid_comp(2)
            naturality2'\<^sub>E(1) residuation.con_implies_arr(2) simulation.preserves_resid
            transformation.naturality1_ax transformation.naturality2_ax
            transformation.preserves_con(2) transformation_axioms
            weakly_extensional_rts.con_imp_eq_src weakly_extensional_rts.src_resid)
      show "F x \\\<^sub>B \<tau> y = G (x \\\<^sub>A y)"
        using assms
        by (metis A.con_sym A.src_resid B.resid_comp(1) F.preserves_resid
            naturality1'\<^sub>E(1) naturality2 preserves_con(2))
    qed

    (*
     * TODO: Does this hold more generally?  I didn't immediately see how to generalize
     * the proof.
     *)
    lemma preserves_prfx:
    assumes "t \<lesssim>\<^sub>A u"
    shows "\<tau> t \<lesssim>\<^sub>B \<tau> u"
    proof -
      have "\<tau> t \\\<^sub>B \<tau> u = B.trg (\<tau> (A.src t)) \\\<^sub>B (F u \\\<^sub>B \<tau> (A.src t)) \<squnion>\<^sub>B
                            B.trg (F u) \\\<^sub>B (\<tau> (A.src t) \\\<^sub>B F u)"
      proof -
        have "\<tau> t \\\<^sub>B \<tau> u = (\<tau> (A.src t) \<squnion>\<^sub>B F t) \\\<^sub>B (\<tau> (A.src t) \<squnion>\<^sub>B F u)"
          by (metis A.con_imp_eq_src A.prfx_implies_con assms naturality3'\<^sub>E(1))
        also have "... = (\<tau> (A.src t) \\\<^sub>B (\<tau> (A.src t) \<squnion>\<^sub>B F u)) \<squnion>\<^sub>B
                         (F t \\\<^sub>B (\<tau> (A.src t) \<squnion>\<^sub>B F u))"
          by (metis assms calculation A.con_implies_arr(2) A.con_sym
              A.prfx_implies_con B.arr_resid_iff_con B.con_sym B.resid_join\<^sub>E(3)
              naturality3'\<^sub>E(2) preserves_con(1))
        also have "... = (\<tau> (A.src t) \\\<^sub>B \<tau> (A.src t)) \\\<^sub>B (F u \\\<^sub>B \<tau> (A.src t)) \<squnion>\<^sub>B
                           (F t \\\<^sub>B F u) \\\<^sub>B (\<tau> (A.src t) \\\<^sub>B F u)"
          by (metis (full_types) assms calculation A.prfx_implies_con
              B.arr_prfx_join_self B.conE B.conI B.join_def B.prfx_implies_con
              B.resid_join\<^sub>E(1-2) B.null_is_zero(2) preserves_con(1))
        also have "... = B.trg (\<tau> (A.src t)) \\\<^sub>B (F u \\\<^sub>B \<tau> (A.src t)) \<squnion>\<^sub>B
                           B.trg (F u) \\\<^sub>B (\<tau> (A.src t) \\\<^sub>B F u)"
          by (metis A.arr_resid_iff_con A.con_implies_arr(2) A.ide_implies_arr
              A.src_ide A.src_resid B.trg_def F.preserves_resid F.preserves_trg
              assms)
        finally show ?thesis by blast
      qed
      moreover have "B.ide ..."
      proof -
        have "B.ide (B.trg (\<tau> (A.src t)) \\\<^sub>B (F u \\\<^sub>B \<tau> (A.src t)))"
          by (metis assms A.con_imp_eq_src A.con_implies_arr(2) A.cong_reflexive
              A.ide_src A.prfx_implies_con A.resid_src_arr A.trg_def naturality2
              preserves_trg G.preserves_prfx)
        moreover have "B.ide (B.trg (F u) \\\<^sub>B (\<tau> (A.src t) \\\<^sub>B F u))"
          using B.apex_sym B.cube B.trg_def calculation by force
        ultimately show ?thesis
          by (metis B.apex_sym B.ide_iff_src_self B.ide_implies_arr
              B.join_arr_self B.prfx_implies_con B.src_resid)
      qed
      ultimately show ?thesis by simp
    qed

  end

  (*
   * TODO: The (strong) extensionality assumption on B is used to guarantee the
   * existence of unique joins, so that the definition of map makes sense.
   * It might be possible to replace this by weak extensionality if the "joinable"
   * locale assumption is strengthened to state that exactly one join exists for
   * the indicated transitions.
   *)

  locale transformation_by_components =
    A: weakly_extensional_rts A +
    B: extensional_rts B + 
    F: simulation A B F +
    G: simulation A B G
  for A :: "'a resid"      (infix "\\\<^sub>A" 55)
  and B :: "'b resid"      (infix "\\\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes preserves_src: "A.ide a \<Longrightarrow> B.src (\<tau> a) = F a"
  and preserves_trg: "A.ide a \<Longrightarrow> B.trg (\<tau> a) = G a"
  and naturality1: "A.arr t \<Longrightarrow> \<tau> (A.src t) \\\<^sub>B F t = \<tau> (A.trg t)"
  and naturality2: "A.arr t \<Longrightarrow> F t \\\<^sub>B \<tau> (A.src t) = G t"
  and joinable: "A.arr t \<Longrightarrow> B.joinable (\<tau> (A.src t)) (F t)"
  begin

    notation B.comp  (infixr "\<cdot>\<^sub>B" 55)
    notation B.join  (infix "\<squnion>\<^sub>B" 52)

    definition map
    where "map t = \<tau> (A.src t) \<squnion>\<^sub>B F t"

    lemma map_eq:
    shows "map t = (if A.arr t then \<tau> (A.src t) \<squnion>\<^sub>B F t else B.null)"
      unfolding map_def
      by (metis B.conE B.join_def B.joinable_implies_con B.null_is_zero(2)
          F.extensional)

    lemma map_simp_ide [simp]:
    assumes "A.ide a"
    shows "map a = \<tau> a"
      using assms map_def
      by (metis A.ide_iff_src_self A.ide_implies_arr B.arr_trg_iff_arr B.join_src
          B.join_sym G.preserves_ide preserves_src preserves_trg B.ide_implies_arr)

    sublocale transformation A B F G map
      using map_eq preserves_src preserves_trg naturality1 naturality2 joinable
      apply (unfold_locales, simp_all)
          apply (metis A.ide_implies_arr A.src_ide B.src_join)
         apply (metis A.ide_implies_arr A.src_ide A.trg_ide B.trg_join)
        apply (metis A.arr_src_iff_arr A.arr_trg_iff_arr A.ide_src A.src_src A.src_trg
          map_simp_ide)
       apply (metis A.arr_src_iff_arr A.ide_src A.src_src map_simp_ide)
      by (metis A.arr_src_iff_arr A.ide_src A.src_src B.join_is_join_of map_simp_ide)

    lemma is_transformation:
    shows "transformation A B F G map"
      ..

  end

  locale identity_transformation =
    transformation +
  assumes identity: "A.ide a \<Longrightarrow> B.ide (\<tau> a)"
  begin

    lemma src_eq_trg:
    shows "F = G"
    proof
      fix x
      show "F x = G x"
        by (metis A.ide_src B.ideE B.resid_arr_src B.src_eqI B.src_join_of(1-2)
          F.extensional F.preserves_reflects_arr G.extensional identity
          naturality3 naturality2)
    qed

    sublocale simulation ..

  end

  lemma comp_identity_transformation:
  assumes "transformation A B F G T"
  shows "I B \<circ> T = T"
    using assms transformation.extensional transformation.preserves_arr
    by fastforce

  lemma comp_transformation_identity:
  assumes "transformation A B F G T"
  shows "T \<circ> I A = T"
    using assms residuation.not_arr_null rts.axioms(1) transformation.extensional
          transformation_def simulation_def
    by fastforce

  locale constant_transformation =
    A: weakly_extensional_rts A +
    B: weakly_extensional_rts B
  for A :: "'a resid"      (infix "\\\<^sub>A" 70)
  and B :: "'b resid"      (infix "\\\<^sub>B" 70)
  and t :: 'b +
  assumes arr_t: "B.arr t"
  begin

    abbreviation map
    where "map x \<equiv> if A.arr x then t else B.null"

    abbreviation F
    where "F \<equiv> constant_simulation.map A B (B.src t)"

    abbreviation G
    where "G \<equiv> constant_simulation.map A B (B.trg t)"

    interpretation F: simulation A B F
      using arr_t A.con_implies_arr B.resid_arr_ide
      by unfold_locales auto

    interpretation G: simulation A B G
      using arr_t A.con_implies_arr B.resid_arr_ide
      by unfold_locales auto

    sublocale transformation A B F G map
      using arr_t B.join_of_arr_src(2)
      by unfold_locales auto

  end

  locale simulation_as_transformation =
    simulation +
    A: weakly_extensional_rts A +
    B: weakly_extensional_rts B
  begin

    sublocale transformation A B F F F
      using extensional A.con_arr_src(1-2) B.join_of_arr_src(1)
      apply unfold_locales
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp (metis A.con_arr_src(2) A.resid_src_arr preserves_resid)
      subgoal by simp (metis A.con_arr_src(1) A.resid_arr_src preserves_resid)
      subgoal by simp
      done

    sublocale identity_transformation A B F F F
      by unfold_locales auto

  end

  lemma transformation_eqI:
  assumes "transformation A B F G \<sigma>" and "transformation A B F G \<tau>"
  and "extensional_rts B"
  and "\<And>a. residuation.ide A a \<Longrightarrow> \<sigma> a = \<tau> a"
  shows "\<sigma> = \<tau>"
  proof
    interpret A: weakly_extensional_rts A
      using assms(1) simulation.axioms(1) transformation_def by blast
    interpret B: extensional_rts B
      using assms(3) by simp
    interpret F: simulation A B F
      using assms(1) transformation.axioms(3) by blast
    interpret G: simulation A B G
      using assms(1) transformation.axioms(4) by blast
    interpret \<sigma>: transformation A B F G \<sigma>
      using assms(1) by blast
    interpret \<tau>: transformation A B F G \<tau>
      using assms(2) by blast
    fix t
    show "\<sigma> t = \<tau> t"
      by (metis A.ide_src B.join_of_unique \<sigma>.extensional \<sigma>.naturality3
          \<tau>.extensional \<tau>.naturality3 assms(4))
  qed

  lemma invertible_simulation_cancel_left':
  assumes "invertible_simulation A B H"
  shows "\<lbrakk>transformation C A F G S; transformation C A F G T;
          H \<circ> S = H \<circ> T\<rbrakk>
            \<Longrightarrow> S = T"
  proof -
    obtain K where K: "inverse_simulations A B K H"
      using assms(1) invertible_simulation.invertible by blast
    interpret HK: inverse_simulations A B K H
      using K by blast
    show "\<lbrakk>transformation C A F G S; transformation C A F G T;
           H \<circ> S = H \<circ> T\<rbrakk>
             \<Longrightarrow> S = T"
      by (metis HK.inv' HOL.ext comp_def transformation.extensional
          transformation.preserves_arr)
  qed

  lemma invertible_simulation_cancel_right':
  assumes "invertible_simulation A B H"
  shows "\<lbrakk>transformation B C F G S; transformation B C F G T;
          S \<circ> H = T \<circ> H\<rbrakk>
            \<Longrightarrow> S = T"
  proof -
    obtain K where K: "inverse_simulations A B K H"
      using assms(1) invertible_simulation.invertible by blast
    interpret HK: inverse_simulations A B K H
      using K by blast
    show "\<lbrakk>transformation B C F G S; transformation B C F G T;
           S \<circ> H = T \<circ> H\<rbrakk>
             \<Longrightarrow> S = T"
      by (metis HK.inv HOL.ext comp_def transformation.extensional)
  qed

  section "Binary Simulations"

  locale binary_simulation_between_weakly_extensional_rts =
    binary_simulation +
    A1: weakly_extensional_rts A1 +
    A0: weakly_extensional_rts A0 +
    B: weakly_extensional_rts B
  begin

    interpretation A: product_of_weakly_extensional_rts A1 A0 ..
    sublocale simulation_to_weakly_extensional_rts A.resid B F ..

    lemma fixing_arr_gives_transformation_1:
    assumes "A1.arr t1"
    shows "transformation A0 B
             (\<lambda>t0. F (A1.src t1, t0)) (\<lambda>t0. F (A1.trg t1, t0))
             (\<lambda>t0. F (t1, t0))"
    proof -
      interpret Fsrc: simulation A0 B \<open>\<lambda>t0. F (A1.src t1, t0)\<close>
        using assms fixing_ide_gives_simulation_1 by simp
      interpret Fsrc: simulation_to_weakly_extensional_rts A0 B
                        \<open>\<lambda>t0. F (A1.src t1, t0)\<close>
        ..
      interpret Ftrg: simulation A0 B \<open>\<lambda>t0. F (A1.trg t1, t0)\<close>
        using assms fixing_ide_gives_simulation_1 by simp
      interpret Ftrg: simulation_to_weakly_extensional_rts A0 B
                        \<open>\<lambda>t0. F (A1.trg t1, t0)\<close>
        ..
      show "transformation A0 B
              (\<lambda>t0. F (A1.src t1, t0)) (\<lambda>t0. F (A1.trg t1, t0))
              (\<lambda>t0. F (t1, t0))"
      proof
        show "\<And>f. \<not> A0.arr f \<Longrightarrow> F (t1, f) = B.null"
          by (simp add: extensional)
        show "\<And>f. A0.ide f \<Longrightarrow> B.src (F (t1, f)) = F (A1.src t1, f)"
          using assms B.src_eqI by simp
        show "\<And>f. A0.ide f \<Longrightarrow> B.trg (F (t1, f)) = F (A1.trg t1, f)"
          by (metis assms fixing_ide_gives_simulation_0 simulation.preserves_trg)
        fix f
        assume f: "A0.arr f"
        show "F (t1, A0.src f) \\\<^sub>B F (A1.src t1, f) = F (t1, A0.trg f)"
        proof -
          have "F (t1, A0.src f) \\\<^sub>B F (A1.src t1, f) =
                F (A.resid (t1, A0.src f) (A1.src t1, f))"
            by (simp add: assms f)
          also have "... = F (t1, A0.trg f)"
            by (simp add: assms f A.resid_def)
          finally show ?thesis by blast
        qed
        show "F (A1.src t1, f) \\\<^sub>B F (t1, A0.src f) = F (A1.trg t1, f)"
        proof -
          have "F (A1.src t1, f) \\\<^sub>B F (t1, A0.src f) =
                F (A.resid (A1.src t1, f) (t1, A0.src f))"
            by (simp add: assms f)
          also have "... = F (A1.trg t1, f)"
            by (simp add: assms f A.resid_def)
          finally show ?thesis by blast
        qed
        show "B.join_of (F (t1, A0.src f)) (F (A1.src t1, f)) (F (t1, f))"
          by (simp add: f A1.join_of_arr_src(2) A0.join_of_arr_src(1)
              assms preserves_joins A.join_of_char(1))
      qed
    qed

    lemma fixing_arr_gives_transformation_0:
    assumes "A0.arr t2"
    shows "transformation A1 B
             (\<lambda>t1. F (t1, A0.src t2)) (\<lambda>t1. F (t1, A0.trg t2))
             (\<lambda>t1. F (t1, t2))"
    proof -
      interpret Fsrc: simulation A1 B \<open>\<lambda>t1. F (t1, A0.src t2)\<close>
        using assms fixing_ide_gives_simulation_0 by simp
      interpret Fsrc: simulation_to_weakly_extensional_rts A1 B
        \<open>\<lambda>t1. F (t1, A0.src t2)\<close>
        ..
      interpret Ftrg: simulation A1 B \<open>\<lambda>t1. F (t1, A0.trg t2)\<close>
        using assms fixing_ide_gives_simulation_0 by simp
      interpret Ftrg: simulation_to_weakly_extensional_rts A1 B
                        \<open>\<lambda>t1. F (t1, A0.trg t2)\<close>
        ..
      show "transformation A1 B
              (\<lambda>t1. F (t1, A0.src t2)) (\<lambda>t1. F (t1, A0.trg t2))
              (\<lambda>t1. F (t1, t2))"
      proof
        show "\<And>f. \<not> A1.arr f \<Longrightarrow> F (f, t2) = B.null"
          by (simp add: extensional)
        show "\<And>f. A1.ide f \<Longrightarrow> B.src (F (f, t2)) = F (f, A0.src t2)"
          using assms B.src_eqI by simp
        show "\<And>f. A1.ide f \<Longrightarrow> B.trg (F (f, t2)) = F (f, A0.trg t2)"
          by (metis assms fixing_ide_gives_simulation_1 simulation.preserves_trg)
        fix f
        assume f: "A1.arr f"
        show "F (A1.src f, t2) \\\<^sub>B F (f, A0.src t2) = F (A1.trg f, t2)"
          using f fixing_arr_gives_transformation_1 transformation.naturality2
          by fastforce
        show "F (f, A0.src t2) \\\<^sub>B F (A1.src f, t2) = F (f, A0.trg t2)"
          by (metis assms f fixing_arr_gives_transformation_1
              transformation.naturality1_ax)
        show "\<And>f. A1.arr f \<Longrightarrow>
                    B.join_of (F (A1.src f, t2)) (F (f, A0.src t2)) (F (f, t2))"
          by (simp add: A1.join_of_arr_src(1) A0.join_of_arr_src(2)
              assms preserves_joins A.join_of_char(1))
      qed
    qed

  end

  locale transformation_of_binary_simulations =
    A1: weakly_extensional_rts A1 +
    A0: weakly_extensional_rts A0 +
    B: weakly_extensional_rts B +
    A1xA0: product_rts A1 A0 +
    F: binary_simulation A1 A0 B F +
    G: binary_simulation A1 A0 B G +
    transformation A1xA0.resid B F G \<tau>
  for A1 :: "'a1 resid"     (infix "\\\<^sub>A\<^sub>1" 55)
  and A0 :: "'a0 resid"     (infix "\\\<^sub>A\<^sub>0" 55)
  and B :: "'b resid"       (infix "\\\<^sub>B" 55)
  and F :: "'a1 * 'a0 \<Rightarrow> 'b"
  and G :: "'a1 * 'a0 \<Rightarrow> 'b"
  and \<tau> :: "'a1 * 'a0 \<Rightarrow> 'b"
  begin

    notation A0.con     (infix "\<frown>\<^sub>A\<^sub>0" 50)
    notation A0.prfx    (infix "\<lesssim>\<^sub>A\<^sub>0" 50)
    notation A0.cong    (infix "\<sim>\<^sub>A\<^sub>0" 50)

    notation A1.con     (infix "\<frown>\<^sub>A\<^sub>1" 50)
    notation A1.prfx    (infix "\<lesssim>\<^sub>A\<^sub>1" 50)
    notation A1.cong    (infix "\<sim>\<^sub>A\<^sub>1" 50)

    notation B.con     (infix "\<frown>\<^sub>B" 50)
    notation B.prfx    (infix "\<lesssim>\<^sub>B" 50)
    notation B.cong    (infix "\<sim>\<^sub>B" 50)

    notation A1xA0.resid    (infix "\\\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>0" 55)

    sublocale A1xA0: product_of_weakly_extensional_rts A1 A0 ..

    lemma fixing_ide_gives_transformation_1:
    assumes "A1.ide a1"
    shows "transformation A0 B (\<lambda>f0. F (a1, f0)) (\<lambda>f0. G (a1, f0))
             (\<lambda>f0. \<tau> (a1, f0))"
    proof -
      interpret Fa1: simulation A0 B \<open>\<lambda>f0. F (a1, f0)\<close>
        using assms F.fixing_ide_gives_simulation_1 by simp
      interpret Ga1: simulation A0 B \<open>\<lambda>f0. G (a1, f0)\<close>
        using assms "G.fixing_ide_gives_simulation_1" by simp
      show ?thesis
      proof
        fix f
        show "\<not> A0.arr f \<Longrightarrow> \<tau> (a1, f) = B.null"
          by (simp add: extensional)
        show "A0.ide f \<Longrightarrow> B.src (\<tau> (a1, f)) = F (a1, f)"
          using assms preserves_src by force
        show "A0.ide f \<Longrightarrow> B.trg (\<tau> (a1, f)) = G (a1, f)"
          by (simp add: assms preserves_trg)
        show "A0.arr f \<Longrightarrow> \<tau> (a1, A0.src f) \\\<^sub>B F (a1, f) = \<tau> (a1, A0.trg f)"
          by (metis A1.ide_iff_src_self A1.ide_iff_trg_self A1.ide_implies_arr
              A1xA0.src_char A1xA0.trg_char F.preserves_reflects_arr
              Fa1.preserves_reflects_arr assms fst_conv naturality1 snd_conv)
        show "A0.arr f \<Longrightarrow> F (a1, f) \\\<^sub>B \<tau> (a1, A0.src f) = G (a1, f)"
          by (metis assms A1.ide_iff_src_self A1.ide_implies_arr A1xA0.src_char
              G.preserves_reflects_arr Ga1.preserves_reflects_arr fst_conv
              naturality2 snd_conv)
        show "A0.arr f \<Longrightarrow> B.join_of (\<tau> (a1, A0.src f)) (F (a1, f)) (\<tau> (a1, f))"
          by (metis assms A1.ide_iff_src_self A1.ide_implies_arr A1xA0.src_char
              G.preserves_reflects_arr Ga1.preserves_reflects_arr fst_conv naturality3
              snd_conv)
      qed
    qed

    lemma fixing_ide_gives_transformation_0:
    assumes "A0.ide a0"
    shows "transformation A1 B (\<lambda>f1. F (f1, a0)) (\<lambda>f1. G (f1, a0))
             (\<lambda>f1. \<tau> (f1, a0))"
    proof -
      interpret Fa0: simulation A1 B \<open>\<lambda>f1. F (f1, a0)\<close>
        using assms F.fixing_ide_gives_simulation_0 by simp
      interpret Ga0: simulation A1 B \<open>\<lambda>f1. G (f1, a0)\<close>
        using assms "G.fixing_ide_gives_simulation_0" by simp
      show ?thesis
      proof
        fix f
        show "\<not> A1.arr f \<Longrightarrow> \<tau> (f, a0) = B.null"
          by (simp add: extensional)
        show "A1.ide f \<Longrightarrow> B.src (\<tau> (f, a0)) = F (f, a0)"
          by (simp add: assms preserves_src)
        show "A1.ide f \<Longrightarrow> B.trg (\<tau> (f, a0)) = G (f, a0)"
          by (simp add: assms preserves_trg)
        show "A1.arr f \<Longrightarrow> \<tau> (A1.src f, a0) \\\<^sub>B F (f, a0) = \<tau> (A1.trg f, a0)"
          by (metis A1xA0.src_char A1xA0.trg_char A0.ide_iff_src_self
              A0.ide_iff_trg_self A0.ide_implies_arr F.preserves_reflects_arr
              Fa0.preserves_reflects_arr assms fst_conv naturality1 snd_conv)
        show "A1.arr f \<Longrightarrow> F (f, a0) \\\<^sub>B \<tau> (A1.src f, a0) = G (f, a0)"
          by (metis A1xA0.src_char A0.ide_iff_src_self A0.ide_implies_arr
              F.preserves_reflects_arr Fa0.preserves_reflects_arr assms
              fst_conv naturality2 snd_conv)
        show "A1.arr f \<Longrightarrow> B.join_of (\<tau> (A1.src f, a0)) (F (f, a0)) (\<tau> (f, a0))"
          by (metis A1xA0.src_char A0.ide_iff_src_self A0.ide_implies_arr
              F.preserves_reflects_arr Fa0.preserves_reflects_arr assms
              fst_conv naturality3 snd_conv)
      qed
    qed

  end

  section "Horizontal Composite of Transformations"

  lemma transformation_whisker_left:
  assumes "transformation A B F G \<tau>" and "simulation B C H"
  and "weakly_extensional_rts C"
  shows "transformation A C (H \<circ> F) (H \<circ> G) (H \<circ> \<tau>)"
  proof -
    interpret C: weakly_extensional_rts C
      using assms(3) by blast
    interpret \<tau>: transformation A B F G \<tau>
      using assms by blast
    interpret H: simulation B C H
      using assms by blast
    interpret HoF: composite_simulation A B C F H ..
    interpret HoG: composite_simulation A B C G H ..
    show ?thesis
    proof
      fix t
      show "\<not> \<tau>.A.arr t \<Longrightarrow> (H \<circ> \<tau>) t = C.null"
        by (simp add: H.extensional \<tau>.extensional)
      show "\<tau>.A.ide t \<Longrightarrow> C.src ((H \<circ> \<tau>) t) = HoF.map t"
        by (metis C.src_eqI H.preserves_con HoF.preserves_ide \<tau>.A.ide_implies_arr
            \<tau>.B.con_arr_src(2) \<tau>.preserves_arr \<tau>.preserves_src comp_eq_dest_lhs)
      show "\<tau>.A.ide t \<Longrightarrow> C.trg ((H \<circ> \<tau>) t) = HoG.map t"
        by (metis H.preserves_trg \<tau>.A.ide_implies_arr \<tau>.preserves_arr
            \<tau>.preserves_trg comp_apply)
      show "\<tau>.A.arr t \<Longrightarrow>
              C ((H \<circ> \<tau>) (\<tau>.A.src t)) (HoF.map t) = (H \<circ> \<tau>) (\<tau>.A.trg t)"
        by (metis H.preserves_resid \<tau>.B.conI \<tau>.B.con_sym_ax \<tau>.B.not_arr_null
            \<tau>.G.preserves_reflects_arr \<tau>.naturality1_ax \<tau>.naturality2_ax comp_apply)
      show "\<tau>.A.arr t \<Longrightarrow> C (HoF.map t) ((H \<circ> \<tau>) (\<tau>.A.src t)) = HoG.map t"
        by (metis H.preserves_resid \<tau>.B.arr_resid_iff_con \<tau>.G.preserves_reflects_arr
            \<tau>.naturality2_ax comp_apply)
      show "\<tau>.A.arr t \<Longrightarrow> C.join_of ((H \<circ> \<tau>) (\<tau>.A.src t)) (HoF.map t) ((H \<circ> \<tau>) t)"
        by (metis H.simulation_axioms \<tau>.naturality3 comp_apply
            simulation.preserves_joins)
    qed
  qed

  lemma transformation_whisker_right:
  assumes "transformation B C F G \<tau>" and "simulation A B H"
  and "weakly_extensional_rts A"
  shows "transformation A C (F \<circ> H) (G \<circ> H) (\<tau> \<circ> H)"
  proof -
    interpret A: weakly_extensional_rts A
      using assms(3) by blast
    interpret \<tau>: transformation B C F G \<tau>
      using assms by blast
    interpret H: simulation A B H
      using assms by blast
    interpret FoH: composite_simulation A B C H F ..
    interpret GoH: composite_simulation A B C H G ..
    show ?thesis
    proof
      fix t
      show "\<not> A.arr t \<Longrightarrow> (\<tau> \<circ> H) t = \<tau>.B.null"
        by (simp add: \<tau>.extensional)
      show "A.ide t \<Longrightarrow> \<tau>.B.src ((\<tau> \<circ> H) t) = FoH.map t"
        by (simp add: \<tau>.preserves_src)
      show "A.ide t \<Longrightarrow> \<tau>.B.trg ((\<tau> \<circ> H) t) = GoH.map t"
        by (simp add: \<tau>.preserves_trg)
      show "A.arr t \<Longrightarrow> C ((\<tau> \<circ> H) (A.src t)) (FoH.map t) = (\<tau> \<circ> H) (A.trg t)"
        by (metis A.arr_has_un_source A.arr_src_iff_arr A.con_arr_src(1)
            A.src_in_sources A.trg_src H.preserves_con H.preserves_trg
            \<tau>.A.con_imp_eq_src \<tau>.A.src_trg \<tau>.naturality1 comp_def)
      show "A.arr t \<Longrightarrow> C (FoH.map t) ((\<tau> \<circ> H) (A.src t)) = GoH.map t"
        by (metis A.con_arr_src(2) A.ide_src H.preserves_con H.preserves_ide
            \<tau>.A.con_imp_eq_src \<tau>.naturality2 comp_apply \<tau>.A.src_ide)
      show "A.arr t \<Longrightarrow> \<tau>.B.join_of ((\<tau> \<circ> H) (A.src t)) (FoH.map t) ((\<tau> \<circ> H) t)"
        by (metis (full_types) A.con_arr_src(2) A.ide_src FoH.preserves_reflects_arr
            H.preserves_con H.preserves_ide \<tau>.B.not_arr_null
            \<tau>.F.extensional \<tau>.naturality3 comp_apply \<tau>.A.con_imp_eq_src \<tau>.A.src_ide)
    qed
  qed

  text\<open>
    Horizontal composition of transformations requires reasoning about joins
    which it is not clear that it is possible to do unless extensionality is assumed.
  \<close>

  lemma horizontal_composite:
  assumes "transformation B C F G \<sigma>" and "transformation A B H K \<tau>"
  and "extensional_rts A" and "extensional_rts B" and "extensional_rts C"
  shows "transformation A C (F \<circ> H) (G \<circ> K) (\<sigma> \<circ> \<tau>)"
  proof -
    interpret A: extensional_rts A
      using assms(3) by blast
    interpret B: extensional_rts B
      using assms(4) by blast
    interpret C: extensional_rts C
      using assms(5) by blast
    interpret \<sigma>: transformation B C F G \<sigma>
      using assms by blast
    interpret \<sigma>: transformation_to_extensional_rts B C F G \<sigma> ..
    interpret \<tau>: transformation A B H K \<tau>
      using assms by blast
    interpret \<tau>: transformation_to_extensional_rts A B H K \<tau> ..
    interpret FoH: composite_simulation A B C H F ..
    interpret GoH: composite_simulation A B C H G ..
    interpret FoK: composite_simulation A B C K F ..
    interpret GoK: composite_simulation A B C K G ..
    show ?thesis
    proof
       write A  (infix "\\\<^sub>A" 55)
       write B  (infix "\\\<^sub>B" 55)
       write C  (infix "\\\<^sub>C" 55)
       write B.join  (infixr "\<squnion>\<^sub>B" 52)
       write C.join  (infixr "\<squnion>\<^sub>C" 52)
       fix t
       show "\<not> A.arr t \<Longrightarrow> (\<sigma> \<circ> \<tau>) t = C.null"
         by (simp add: \<sigma>.extensional \<tau>.extensional)
       show "A.ide t \<Longrightarrow> C.src ((\<sigma> \<circ> \<tau>) t) = FoH.map t"
         by (metis A.arr_def A.ideE C.weakly_extensional_rts_axioms \<sigma>.naturality3
             \<sigma>.transformation_axioms \<tau>.F.preserves_ide \<tau>.preserves_arr \<tau>.preserves_src
             comp_apply transformation.preserves_src weakly_extensional_rts.src_join_of(1))
       show "A.ide t \<Longrightarrow> C.trg ((\<sigma> \<circ> \<tau>) t) = GoK.map t"
         by (metis A.arr_resid_iff_con A.ideE C.apex_sym C.trg_join_of(1)
             \<sigma>.G.preserves_trg \<sigma>.naturality2 \<sigma>.naturality3 \<tau>.preserves_arr
             \<tau>.preserves_trg comp_apply)
       assume t: "A.arr t"
       show "(\<sigma> \<circ> \<tau>) (A.src t) \\\<^sub>C FoH.map t = (\<sigma> \<circ> \<tau>) (A.trg t)"
         by (simp add: \<sigma>.general_naturality(1) \<tau>.naturality1_ax
             \<tau>.preserves_con(2) t)
       show "FoH.map t \\\<^sub>C (\<sigma> \<circ> \<tau>) (A.src t) = GoK.map t"
         by (simp add: B.con_sym \<sigma>.general_naturality(2) \<tau>.naturality2_ax
             \<tau>.preserves_con(2) t)
       show "C.join_of ((\<sigma> \<circ> \<tau>) (A.src t)) (FoH.map t) ((\<sigma> \<circ> \<tau>) t)"
       proof -
         have "\<sigma> (\<tau> (A.src t)) \<squnion>\<^sub>C F (H t) = \<sigma> (\<tau> t)"
         proof (intro C.join_eqI)
           show 1: "C.prfx (\<sigma> (\<tau> (A.src t))) (\<sigma> (\<tau> t))"
             using t \<tau>.preserves_prfx \<sigma>.preserves_prfx by simp
           show 2: "C.prfx (F (H t)) (\<sigma> (\<tau> t))"
             using t
             by (meson C.composite_ofE C.prfx_transitive \<sigma>.F.preserves_composites
                 \<sigma>.naturality1' \<tau>.naturality1' \<tau>.preserves_arr)
           show 3: "\<sigma> (\<tau> t) \\\<^sub>C F (H t) = \<sigma> (\<tau> (A.src t)) \\\<^sub>C F (H t)"
             by (simp add: A.trg_def \<sigma>.general_naturality(1) \<tau>.general_naturality(1)
                 \<tau>.preserves_con(2) t)
           show "\<sigma> (\<tau> t) \\\<^sub>C \<sigma> (\<tau> (A.src t)) = F (H t) \\\<^sub>C \<sigma> (\<tau> (A.src t))"
             using t 1 2 3 C.apex_arr_prfx(1) C.apex_sym C.cube C.extensional
	           C.ideE C.trg_def
             by (smt (verit, del_insts))
         qed
         thus ?thesis
           using t
           by (metis C.join_is_join_of C.joinable_iff_arr_join \<sigma>.preserves_arr
               \<tau>.preserves_arr comp_apply)
       qed
     qed
   qed

end
