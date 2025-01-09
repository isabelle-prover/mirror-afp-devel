(*  Title:       Preliminaries_RTS
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

theory Preliminaries
imports Main "HOL-Library.FuncSet"
        ResiduatedTransitionSystem.ResiduatedTransitionSystem
begin

section "Simulations"

  abbreviation I
  where "I \<equiv> identity_simulation.map"

  lemma comp_identity_simulation:
  assumes "simulation A B F"
  shows "I B \<circ> F = F"
    using assms simulation.extensionality simulation.preserves_reflects_arr
    by fastforce

  lemma comp_simulation_identity:
  assumes "simulation A B F"
  shows "F \<circ> I A = F"
    using assms residuation.not_arr_null rts.axioms(1) simulation.extensionality
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
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
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
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
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

    lemma preserve_sources_exactly:
    assumes "B.arr t"
    shows "A.sources (F t) = F ` B.sources t"
    proof
      show "F ` B.sources t \<subseteq> A.sources (F t)"
        using F.preserves_sources by auto
      show "A.sources (F t) \<subseteq> F ` B.sources t"
        by (metis A.ide_implies_arr A.source_is_ide G.preserves_sources assms
            image_subset_iff inv'_simp inv_simp subsetI)
    qed

    lemma preserve_targets_exactly:
    assumes "B.arr t"
    shows "A.targets (F t) = F ` B.targets t"
    proof
      show "F ` B.targets t \<subseteq> A.targets (F t)"
        using F.preserves_targets by auto
      show "A.targets (F t) \<subseteq> F ` B.targets t"
        by (metis A.ide_implies_arr A.target_is_ide G.preserves_targets assms
            image_subset_iff inv'_simp inv_simp subsetI)
    qed

    lemma preserve_weakly_extensional_rts:
    assumes "weakly_extensional_rts A"
    shows "weakly_extensional_rts B"
      using assms
      by (metis A.ide_implies_arr B.ide_implies_arr B.rts_axioms
          F.preserves_con F.preserves_ide inv_simp B.prfx_implies_con
          weakly_extensional_rts.con_imp_eq_src weakly_extensional_rts.ide_iff_src_self
          weakly_extensional_rts.intro weakly_extensional_rts_axioms.intro)

    lemma preserve_extensional_rts:
    assumes "extensional_rts A"
    shows "extensional_rts B"
      using assms
      by (metis (full_types) B.con_implies_arr(2) B.rts_axioms extensional_rts.extensionality
          extensional_rts.intro extensional_rts_axioms.intro inv_simp B.prfx_implies_con
          F.preserves_prfx)

    lemma preserve_rts_with_composites:
    assumes "rts_with_composites A"
    shows "rts_with_composites B"
      by (metis B.composable_def B.rts_axioms B.seqE F.preserves_seq G.preserves_composites
          assms inv_simp rts_with_composites.intro rts_with_composites.obtains_composite_of
          rts_with_composites_axioms.intro)

    lemma preserve_rts_with_joins:
    assumes "rts_with_joins A"
    shows "rts_with_joins B"
    proof -
      show "rts_with_joins B"
      proof
        fix t u
        assume con: "B.con t u"
        obtain t' u' where 1: "A.con t' u' \<and> G t' = t \<and> G u' = u"
          using con B.con_implies_arr(1-2) F.preserves_con inv_simp by meson
        have "A.joinable t' u'"
          using assms 1 rts_with_joins.has_joins by auto
        thus "B.joinable t u"
          by (metis "1" A.joinable_def B.joinable_def G.preserves_joins)
      qed
    qed

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
      by (metis F.B.not_con_null(1) F.B.not_con_null(2) F.extensionality FG.F.preserves_con
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
              simulation.extensionality)
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
        by (metis FG'.F.extensionality FG'.F.preserves_reflects_arr FG'.inv FG.F.extensionality
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
      using map_simp by (meson F.extensionality)

  end

  context inverse_simulations
  begin

    lemma inverse_eq:
    shows "inverse_simulation.map A B G = F"
      by (metis G.invertible_simulation_axioms inverse_simulation.intro
          inverse_simulation.map_def inverse_simulation_unique inverse_simulations_axioms
          inverse_simulations_def someI_ex)

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
        by (metis FF'.inv GG'.F.extensionality GG'.F.preserves_reflects_arr
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
                F.extensionality G.extensionality
          by auto
      qed
      show "F'xG'.map \<circ> FxG.map = I AxC.resid"
      proof
        fix t
        show "(F'xG'.map \<circ> FxG.map) t = I AxC.resid t"
          using F'.inv' G'.inv' FxG.map_def F'xG'.map_def
                F'.extensionality G'.extensionality
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
      by (metis HK.inv' HOL.ext comp_def simulation.extensionality
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
      by (metis HK.inv HOL.ext comp_def simulation.extensionality)
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

  lemma isomorphism_cong_props:
  assumes "isomorphic_rts A B"
  shows weakly_extensional_cong_iso: "weakly_extensional_rts A \<Longrightarrow> weakly_extensional_rts B"
  and extensional_cong_iso: "extensional_rts A \<Longrightarrow> extensional_rts B"
  and rts_with_composites_cong_iso: "rts_with_composites A \<Longrightarrow> rts_with_composites B"
  and rts_with_joins_cong_iso: "rts_with_joins A \<Longrightarrow> rts_with_joins B"
  proof -
    obtain F G where FG: "inverse_simulations A B G F"
      using assms(1)
      by (meson invertible_simulation_def' isomorphic_rts_def)
    interpret FG: inverse_simulations A B G F
      using FG by blast
    show "weakly_extensional_rts A \<Longrightarrow> weakly_extensional_rts B"
      using FG.preserve_weakly_extensional_rts by auto
    show "extensional_rts A \<Longrightarrow> extensional_rts B"
      using FG.preserve_extensional_rts by auto
    show "rts_with_composites A \<Longrightarrow> rts_with_composites B"
      using FG.preserve_rts_with_composites by auto
    show "rts_with_joins A \<Longrightarrow> rts_with_joins B"
      using FG.preserve_rts_with_joins by auto
  qed

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
    by (metis A.ide_trg A.trg_def B.conI B.con_implies_arr(2) B.not_ide_null
        assms respects_cong)

  lemma (in transformation) preserves_con:
  assumes "t \<frown>\<^sub>A u"
  shows "\<tau> t \<frown>\<^sub>B \<tau> u" and "\<tau> t \<frown>\<^sub>B F u"
  proof -
    obtain a where a: "a \<in> A.sources t \<inter> A.sources u"
      using assms(1)
      by (meson A.con_imp_common_source all_not_in_conv)
    have 1: "B.join_of (\<tau> a) (F t) (\<tau> t) \<and> B.join_of (\<tau> a) (F u) (\<tau> u)"
      using a naturality3 by auto
    show "\<tau> t \<frown>\<^sub>B \<tau> u"
      by (metis (full_types) "1" B.composite_ofE B.con_composite_of_iff
          B.cong_subst_left(1) B.join_ofE G.simulation_axioms IntD1 IntD2
          a assms naturality2_ax simulation.preserves_con)
    thus "\<tau> t \<frown>\<^sub>B F u"
      using assms
      by (meson "1" B.con_sym B.con_with_join_of_iff(2) B.join_of_symmetric)
  qed

  lemma (in transformation) naturality1':
  assumes "A.arr t"
  shows "B.composite_of (F t) (\<tau> (A.trg t)) (\<tau> t)"
    using assms
    by (metis A.src_in_sources B.join_ofE naturality1 naturality3)

  lemma (in transformation) naturality2':
  assumes "A.arr t"
  shows "B.composite_of (\<tau> (A.src t)) (G t) (\<tau> t)"
    by (metis A.src_in_sources B.join_ofE assms naturality2 naturality3)

  locale transformation_to_extensional_rts =
    transformation +
    B: extensional_rts B
  begin

    notation B.comp  (infixr \<open>\<cdot>\<^sub>B\<close> 55)
    notation B.join  (infixr \<open>\<squnion>\<^sub>B\<close> 52)

    lemma naturality1'\<^sub>E:
    shows "F t \<cdot>\<^sub>B \<tau> (A.trg t) = \<tau> t"
    and "A.arr t \<Longrightarrow> B.composable (F t) (\<tau> (A.trg t))"
    proof -
      show "F t \<cdot>\<^sub>B \<tau> (A.trg t) = \<tau> t"
        using naturality1' B.comp_is_composite_of(2)
        by (metis A.arr_trg_iff_arr B.comp_null(2) extensionality)
      thus "A.arr t \<Longrightarrow> B.composable (F t) (\<tau> (A.trg t))"
        by (simp add: B.composable_iff_arr_comp preserves_arr)
    qed

    lemma naturality2'\<^sub>E:
    shows "\<tau> (A.src t) \<cdot>\<^sub>B G t = \<tau> t"
    and "A.arr t \<Longrightarrow> B.composable (\<tau> (A.src t)) (G t)"
    proof -
      show "\<tau> (A.src t) \<cdot>\<^sub>B G t = \<tau> t"
        using naturality2' B.comp_is_composite_of(2)
        by (metis B.comp_null(2) G.extensionality extensionality)
      thus "A.arr t \<Longrightarrow> B.composable (\<tau> (A.src t)) (G t)"
        by (simp add: B.composable_iff_arr_comp preserves_arr)
    qed

    lemma naturality3'\<^sub>E:
    shows "\<tau> (A.src t) \<squnion>\<^sub>B F t = \<tau> t"
    and "A.arr t \<Longrightarrow> B.joinable (\<tau> (A.src t)) (F t)"
    proof -
      show "\<tau> (A.src t) \<squnion>\<^sub>B F t = \<tau> t"
        using naturality3
        by (metis B.extensional_rts_axioms B.join_expansion(1) B.joinable_iff_composable
            extensionality extensional_rts.join_def naturality2 naturality2'\<^sub>E(1-2))
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
        by (metis A.con_imp_cong_src A.con_implies_arr(2) A.ide_src A.ide_trg
            A.src_resid B.resid_comp(2) G.preserves_resid naturality1 naturality2
            naturality2'\<^sub>E(1) preserves_con(2) respects_cong_ide)
      show "F x \\\<^sub>B \<tau> y = G (x \\\<^sub>A y)"
        using assms
        by (metis A.arr_resid A.con_sym A.ide_src A.src_resid B.resid_comp(1)
            F.preserves_resid naturality1'\<^sub>E(1) naturality2 preserves_con(2)
            respects_cong_ide)
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
          by (metis A.con_imp_cong_src A.con_implies_arr(2) A.ide_src
              A.prfx_implies_con assms naturality3'\<^sub>E(1) respects_cong_ide)
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
          by (metis B.apex_arr_prfx\<^sub>W\<^sub>E(2) B.trg_def B.trg_ide F.preserves_prfx assms)
        finally show ?thesis by blast
      qed
      moreover have "B.ide ..."
      proof -
        have "B.ide (B.trg (\<tau> (A.src t)) \\\<^sub>B (F u \\\<^sub>B \<tau> (A.src t)))"
          by (metis A.not_arr_null A.src_def B.rts_axioms assms
              extensionality B.cong_char naturality2' preserves_con(2)
              A.arr_resid_iff_con B.arr_resid_iff_con B.cube A.ide_implies_arr
              B.trg_def rts.con_prfx_composite_of(2))
        moreover have "B.ide (B.trg (F u) \\\<^sub>B (\<tau> (A.src t) \\\<^sub>B F u))"
          using B.apex_sym B.cube B.trg_def calculation by force
        ultimately show ?thesis
          by (metis B.apex_sym B.ide_iff_src_self B.ide_implies_arr
              B.join_arr_self B.prfx_implies_con B.src_resid\<^sub>W\<^sub>E)
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
    A: rts A +
    B: extensional_rts B + 
    F: simulation A B F +
    G: simulation A B G
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 55)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes preserves_src: "A.ide a \<Longrightarrow> B.src (\<tau> a) = F a"
  and preserves_trg: "A.ide a \<Longrightarrow> B.trg (\<tau> a) = G a"
  and respects_cong_ide: "\<lbrakk>A.ide a; A.cong a a'\<rbrakk> \<Longrightarrow> \<tau> a = \<tau> a'"
  and naturality1: "a \<in> A.sources t \<Longrightarrow> \<tau> a \\\<^sub>B F t = \<tau> (a \\\<^sub>A t)"
  and naturality2: "a \<in> A.sources t \<Longrightarrow> F t \\\<^sub>B \<tau> a = G t"
  and joinable: "a \<in> A.sources t \<Longrightarrow> B.joinable (\<tau> a) (F t)"
  begin

    notation B.comp  (infixr \<open>\<cdot>\<^sub>B\<close> 55)
    notation B.join  (infixr \<open>\<squnion>\<^sub>B\<close> 52)

    definition map
    where "map t = \<tau> (A.src t) \<squnion>\<^sub>B F t"

    lemma map_eq:
    shows "map t = (if A.arr t then \<tau> (A.src t) \<squnion>\<^sub>B F t else B.null)"
      unfolding map_def
      by (metis B.conE B.join_def B.joinable_implies_con B.null_is_zero(2)
          F.extensionality)

    lemma map_simp_ide [simp]:
    assumes "A.ide a"
    shows "map a = \<tau> a"
      using assms map_def
      by (simp add: B.join_prfx(2) naturality2 respects_cong_ide)

    sublocale transformation A B F G map
      using map_eq preserves_src preserves_trg naturality1 naturality2 joinable
      apply (unfold_locales)
            apply presburger
           apply (metis A.ide_backward_stable map_simp_ide respects_cong_ide)
          apply (metis map_simp_ide)
         apply (metis map_simp_ide)
        apply (metis A.in_sourcesE A.source_is_prfx map_simp_ide)
       apply (metis A.in_sourcesE map_simp_ide)
      by (metis A.con_implies_arr(1) A.in_sourcesE A.sources_are_cong
          A.src_in_sources B.join_is_join_of map_simp_ide respects_cong_ide)

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
        by (metis A.con_arr_src(2) A.ide_src B.resid_arr_ide
            F.extensionality G.extensionality identity naturality2 preserves_con(2)
            B.con_sym)
    qed

    sublocale simulation ..

  end

  lemma comp_identity_transformation:
  assumes "transformation A B F G T"
  shows "I B \<circ> T = T"
    using assms transformation.extensionality transformation.preserves_arr
    by fastforce

  lemma comp_transformation_identity:
  assumes "transformation A B F G T"
  shows "T \<circ> I A = T"
    using assms residuation.not_arr_null rts_def transformation.extensionality
          transformation_def
    by fastforce

  locale constant_transformation =
    A: rts A +
    B: weakly_extensional_rts B
  for A :: "'a resid"      (infix \<open>\\<^sub>A\<close> 70)
  and B :: "'b resid"      (infix \<open>\\<^sub>B\<close> 70)
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
      using arr_t B.join_of_arr_src(2) A.ide_backward_stable A.ide_implies_arr
      apply unfold_locales
            apply argo
           apply meson
          apply (metis (full_types))
         apply (metis (full_types))
        apply (metis (full_types) A.arr_iff_has_source A.in_sourcesE A.source_is_prfx
          B.con_arr_src(2) B.con_imp_coinitial B.resid_ide(1) ex_in_conv B.ide_src)
       apply (metis (full_types) A.in_sourcesE B.null_is_zero(1) B.resid_src_arr)
      by (metis (full_types) A.con_implies_arr(1) A.in_sourcesE B.src_in_sources)

  end

  locale simulation_as_transformation =
    simulation +
    B: weakly_extensional_rts B
  begin

    sublocale transformation A B F F F
      using extensionality B.join_of_arr_src(1) A.con_sym B.resid_arr_ide
            A.con_implies_arr(1)
      apply unfold_locales
      by auto (meson B.ide_backward_stable B.weak_extensionality preserves_ide
          preserves_prfx)

    sublocale identity_transformation A B F F F
      by unfold_locales auto

  end

  lemma transformation_eqI:
  assumes "transformation A B F G \<sigma>" and "transformation A B F G \<tau>"
  and "extensional_rts B"
  and "\<And>a. residuation.ide A a \<Longrightarrow> \<sigma> a = \<tau> a"
  shows "\<sigma> = \<tau>"
  proof
    interpret A:rts A
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
      by (metis A.prfx_reflexive A.trg_def B.composite_of_unique \<sigma>.extensionality
          \<sigma>.naturality1' \<tau>.extensionality \<tau>.naturality1' assms(4))
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
      by (metis HK.inv' HOL.ext comp_def transformation.extensionality
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
      by (metis HK.inv HOL.ext comp_def transformation.extensionality)
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
          by (simp add: extensionality)
        show "\<And>f. A0.ide f \<Longrightarrow> B.src (F (t1, f)) = F (A1.src t1, f)"
          using assms B.src_eqI by simp
        show "\<And>f. A0.ide f \<Longrightarrow> B.trg (F (t1, f)) = F (A1.trg t1, f)"
          by (metis assms fixing_ide_gives_simulation_0 simulation.preserves_trg)
        show "\<And>a a'. \<lbrakk>A0.ide a; A0.cong a a'\<rbrakk> \<Longrightarrow> F (t1, a) = F (t1, a')"
          using A0.ide_backward_stable A0.weak_extensionality by blast
        fix a f
        assume f: "a \<in> A0.sources f"
        show "F (t1, a) \\\<^sub>B F (A1.src t1, f) = F (t1, a \\\<^sub>A\<^sub>0 f)"
          by (metis A.resid_def A0.prfx_implies_con
              A1.con_arr_src(1) A1.resid_arr_src assms f fst_conv
              preserves_resid A.con_char A0.source_is_prfx snd_conv)
        show "F (A1.src t1, f) \\\<^sub>B F (t1, a) = F (A1.trg t1, f)"
          by (metis A.resid_def  A1.con_arr_src(2) A1.resid_src_arr assms f
              fst_conv preserves_resid A.con_char A0.in_sourcesE
              A0.resid_arr_ide snd_conv)
        show "B.join_of (F (t1, a)) (F (A1.src t1, f)) (F (t1, f))"
          by (metis A.join_of_char(1) A0.con_implies_arr(2)
              A1.join_of_arr_src(2) A1.src_in_sources assms f fst_conv preserves_joins
              A0.join_of_arr_src(1) A0.prfx_implies_con A0.source_is_prfx snd_conv)
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
          by (simp add: extensionality)
        show "\<And>f. A1.ide f \<Longrightarrow> B.src (F (f, t2)) = F (f, A0.src t2)"
          using assms B.src_eqI by simp
        show "\<And>f. A1.ide f \<Longrightarrow> B.trg (F (f, t2)) = F (f, A0.trg t2)"
          by (metis assms fixing_ide_gives_simulation_1 simulation.preserves_trg)
        show "\<And>a a'. \<lbrakk>A1.ide a; A1.cong a a'\<rbrakk> \<Longrightarrow> F (a, t2) = F (a', t2)"
          using A1.ide_backward_stable A1.weak_extensionality by blast

        fix a f
        assume f: "a \<in> A1.sources f"
        show "F (a, t2) \\\<^sub>B F (f, A0.src t2) = F (a \\\<^sub>A\<^sub>1 f, t2)"
          by (metis A.resid_def A0.resid_arr_src
              A1.prfx_implies_con assms f fst_conv preserves_resid
              A.con_char A0.con_arr_src(1) A1.source_is_prfx snd_conv)
        show "F (f, A0.src t2) \\\<^sub>B F (a, t2) = F (f, A0.trg t2)"
          by (metis A.con_char A.resid_def A0.con_arr_src(2)
              A0.resid_src_arr assms f fst_conv preserves_resid
              A1.in_sourcesE A1.resid_arr_ide snd_conv)
        show "B.join_of (F (a, t2)) (F (f, A0.src t2)) (F (f, t2))"
          by (metis A.join_of_char(1) A0.join_of_arr_src(2) A0.src_in_sources
              A1.in_sourcesE assms f fst_conv preserves_joins
              A1.con_implies_arr(1) A1.join_of_arr_src(1) snd_conv)
      qed
    qed

  end

  locale transformation_of_binary_simulations =
    A1: rts A1 +
    A0: rts A0 +
    B: weakly_extensional_rts B +
    A1xA0: product_rts A1 A0 +
    F: binary_simulation A1 A0 B F +
    G: binary_simulation A1 A0 B G +
    transformation A1xA0.resid B F G \<tau>
  for A1 :: "'a1 resid"     (infix \<open>\\<^sub>A\<^sub>1\<close> 55)
  and A0 :: "'a0 resid"     (infix \<open>\\<^sub>A\<^sub>0\<close> 55)
  and B :: "'b resid"       (infix \<open>\\<^sub>B\<close> 55)
  and F :: "'a1 * 'a0 \<Rightarrow> 'b"
  and G :: "'a1 * 'a0 \<Rightarrow> 'b"
  and \<tau> :: "'a1 * 'a0 \<Rightarrow> 'b"
  begin

    notation A0.con     (infix \<open>\<frown>\<^sub>A\<^sub>0\<close> 50)
    notation A0.prfx    (infix \<open>\<lesssim>\<^sub>A\<^sub>0\<close> 50)
    notation A0.cong    (infix \<open>\<sim>\<^sub>A\<^sub>0\<close> 50)

    notation A1.con     (infix \<open>\<frown>\<^sub>A\<^sub>1\<close> 50)
    notation A1.prfx    (infix \<open>\<lesssim>\<^sub>A\<^sub>1\<close> 50)
    notation A1.cong    (infix \<open>\<sim>\<^sub>A\<^sub>1\<close> 50)

    notation B.con     (infix \<open>\<frown>\<^sub>B\<close> 50)
    notation B.prfx    (infix \<open>\<lesssim>\<^sub>B\<close> 50)
    notation B.cong    (infix \<open>\<sim>\<^sub>B\<close> 50)

    notation A1xA0.resid    (infix \<open>\\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>0\<close> 55)

    sublocale A1xA0: product_rts A1 A0 ..

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
          by (simp add: extensionality)
        show "A0.ide f \<Longrightarrow> B.src (\<tau> (a1, f)) = F (a1, f)"
          using assms preserves_src by force
        show "A0.ide f \<Longrightarrow> B.trg (\<tau> (a1, f)) = G (a1, f)"
          by (simp add: assms preserves_trg)
        show "\<And>a a'. \<lbrakk>A0.ide a; a \<sim>\<^sub>A\<^sub>0 a'\<rbrakk> \<Longrightarrow> \<tau> (a1, a) = \<tau> (a1, a')"
          using A1xA0.prfx_char assms respects_cong_ide by auto
        fix a
        assume f: "a \<in> A0.sources f"
        show "\<tau> (a1, a) \\\<^sub>B F (a1, f) = \<tau> (a1, a \\\<^sub>A\<^sub>0 f)"
        proof -
          have "A1xA0.con (a1, a) (a1, f)"
            using assms f A1xA0.con_char A0.prfx_implies_con A0.source_is_prfx
            by fastforce
          thus ?thesis
            using assms f naturality1_ax A1xA0.resid_def by fastforce
        qed
        show "F (a1, f) \\\<^sub>B \<tau> (a1, a) = G (a1, f)"
          using assms f naturality2_ax by auto
        show "B.join_of (\<tau> (a1, a)) (F (a1, f)) (\<tau> (a1, f))"
          using assms f naturality3 by auto
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
          by (simp add: extensionality)
        show "A1.ide f \<Longrightarrow> B.src (\<tau> (f, a0)) = F (f, a0)"
          by (simp add: assms preserves_src)
        show "A1.ide f \<Longrightarrow> B.trg (\<tau> (f, a0)) = G (f, a0)"
          by (simp add: assms preserves_trg)
        show "\<And>a a'. \<lbrakk>A1.ide a; a \<sim>\<^sub>A\<^sub>1 a'\<rbrakk> \<Longrightarrow> \<tau> (a, a0) = \<tau> (a', a0)"
          using A1xA0.prfx_char assms respects_cong_ide by auto
        fix a
        assume f: "a \<in> A1.sources f"
        show "\<tau> (a, a0) \\\<^sub>B F (f, a0) = \<tau> (a \\\<^sub>A\<^sub>1 f, a0)"
        proof -
          have "A1xA0.con (a, a0) (f, a0)"
            by (simp add: A1.rts_axioms assms f rts.prfx_implies_con rts.source_is_prfx)
          thus ?thesis
            using assms f A1xA0.resid_def
            by (metis A0.ideE A1.source_is_ide A1xA0.con_char A1xA0.con_sym
                A1xA0.ide_char A1xA0.in_sourcesI fst_conv naturality1_ax snd_conv)
        qed
        show "F (f, a0) \\\<^sub>B \<tau> (a, a0) = G (f, a0)"
          using assms f naturality2_ax by auto
        show "B.join_of (\<tau> (a, a0)) (F (f, a0)) (\<tau> (f, a0))"
          using assms f naturality3 by auto
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
        by (simp add: H.extensionality \<tau>.extensionality)
      show "\<tau>.A.ide t \<Longrightarrow> C.src ((H \<circ> \<tau>) t) = HoF.map t"
        by (metis C.src_eqI H.preserves_con HoF.preserves_ide \<tau>.A.ide_implies_arr
            \<tau>.B.con_arr_src(2) \<tau>.preserves_arr \<tau>.preserves_src comp_eq_dest_lhs)
      show "\<tau>.A.ide t \<Longrightarrow> C.trg ((H \<circ> \<tau>) t) = HoG.map t"
        by (metis H.preserves_trg \<tau>.A.ide_implies_arr \<tau>.preserves_arr
            \<tau>.preserves_trg comp_apply)
      show "\<And>a a'. \<lbrakk>\<tau>.A.ide a; \<tau>.A.cong a a'\<rbrakk> \<Longrightarrow> (H \<circ> \<tau>) a = (H \<circ> \<tau>) a'"
        using \<tau>.respects_cong_ide by auto
      fix a
      assume t: "a \<in> \<tau>.A.sources t"
      show "C ((H \<circ> \<tau>) a) (HoF.map t) = (H \<circ> \<tau>) (A a t)"
        by (metis H.preserves_resid \<tau>.A.con_sym \<tau>.A.in_sourcesE \<tau>.naturality1_ax
            \<tau>.preserves_con(2) comp_apply t)
      show "C (HoF.map t) ((H \<circ> \<tau>) a) = HoG.map t"
        by (metis H.preserves_resid \<tau>.A.con_implies_arr(1) \<tau>.A.in_sourcesE
            \<tau>.B.arr_resid_iff_con \<tau>.G.preserves_reflects_arr \<tau>.naturality2_ax
            comp_apply t)
      show "C.join_of ((H \<circ> \<tau>) a) (HoF.map t) ((H \<circ> \<tau>) t)"
        using H.preserves_joins \<tau>.naturality3 t by auto
    qed
  qed

  lemma transformation_whisker_right:
  assumes "transformation B C F G \<tau>" and "simulation A B H"
  and "rts A"
  shows "transformation A C (F \<circ> H) (G \<circ> H) (\<tau> \<circ> H)"
  proof -
    interpret A: rts A
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
        by (simp add: \<tau>.extensionality)
      show "A.ide t \<Longrightarrow> \<tau>.B.src ((\<tau> \<circ> H) t) = FoH.map t"
        by (simp add: \<tau>.preserves_src)
      show "A.ide t \<Longrightarrow> \<tau>.B.trg ((\<tau> \<circ> H) t) = GoH.map t"
        by (simp add: \<tau>.preserves_trg)
      show "\<And>a a'. \<lbrakk>A.ide a; a \<sim>\<^sub>A a'\<rbrakk> \<Longrightarrow> (\<tau> \<circ> H) a = (\<tau> \<circ> H) a'"
        using H.preserves_prfx \<tau>.respects_cong_ide by auto
      fix a
      assume t: "a \<in> A.sources t"
      show "C ((\<tau> \<circ> H) a) (FoH.map t) = (\<tau> \<circ> H) (A a t)"
        using A.prfx_implies_con A.source_is_prfx \<tau>.naturality1_ax t by auto
      show "C (FoH.map t) ((\<tau> \<circ> H) a) = GoH.map t"
        using \<tau>.naturality2_ax t by auto
      show "\<tau>.B.join_of ((\<tau> \<circ> H) a) (FoH.map t) ((\<tau> \<circ> H) t)"
        using \<tau>.naturality3 t by auto
    qed
  qed

  text\<open>
    Horizontal composition of transformations requires reasoning about joins
    which it is not clear that it is possible to do unless extensionality is assumed.
  \<close>

  lemma horizontal_composite:
  assumes "transformation B C F G \<sigma>" and "transformation A B H K \<tau>"
  and "extensional_rts B" and "extensional_rts C"
  shows "transformation A C (F \<circ> H) (G \<circ> K) (\<sigma> \<circ> \<tau>)"
  proof -
    interpret A: rts A
      using assms(2) transformation_def by blast
    interpret B: extensional_rts B
      using assms(3) by blast
    interpret C: extensional_rts C
      using assms(4) by blast
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
       write A  (infix \<open>\\<^sub>A\<close> 55)
       write B  (infix \<open>\\<^sub>B\<close> 55)
       write C  (infix \<open>\\<^sub>C\<close> 55)
       write B.join  (infixr \<open>\<squnion>\<^sub>B\<close> 52)
       write C.join  (infixr \<open>\<squnion>\<^sub>C\<close> 52)
       fix t
       show "\<not> A.arr t \<Longrightarrow> (\<sigma> \<circ> \<tau>) t = C.null"
         by (simp add: \<sigma>.extensionality \<tau>.extensionality)
       show "\<And>a a'. \<lbrakk>A.ide a; a \<sim>\<^sub>A a'\<rbrakk> \<Longrightarrow> (\<sigma> \<circ> \<tau>) a = (\<sigma> \<circ> \<tau>) a'"
         by (simp add: \<tau>.respects_cong_ide)
       show "A.ide t \<Longrightarrow> C.src ((\<sigma> \<circ> \<tau>) t) = FoH.map t"
         by (metis A.residuation_axioms B.rts_axioms C.src_composite_of \<sigma>.naturality2'
             \<sigma>.preserves_src \<tau>.preserves_arr \<tau>.preserves_src comp_apply
             residuation.ide_implies_arr rts.ide_src)
       show "A.ide t \<Longrightarrow> C.trg ((\<sigma> \<circ> \<tau>) t) = GoK.map t"
         by (metis A.ide_implies_arr C.trg_composite_of \<sigma>.G.preserves_trg \<sigma>.naturality2'
             \<tau>.preserves_arr \<tau>.preserves_trg comp_eq_dest_lhs)
       fix a
       assume t: "a \<in> A.sources t"
       show "(\<sigma> \<circ> \<tau>) a \\\<^sub>C FoH.map t = (\<sigma> \<circ> \<tau>) (A a t)"
         by (simp add: A.rts_axioms A.source_is_prfx \<sigma>.general_naturality(1)
             \<tau>.naturality1_ax \<tau>.preserves_con(2) rts.prfx_implies_con t)
       show "FoH.map t \\\<^sub>C (\<sigma> \<circ> \<tau>) a = GoK.map t"
         by (metis A.rts_axioms B.con_sym \<sigma>.general_naturality(2) \<tau>.naturality2_ax
             \<tau>.preserves_con(2) comp_eq_dest_lhs rts.prfx_implies_con rts.source_is_prfx t)
       show "C.join_of ((\<sigma> \<circ> \<tau>) a) (FoH.map t) ((\<sigma> \<circ> \<tau>) t)"
       proof -
         have "\<sigma> (\<tau> a) \<squnion>\<^sub>C F (H t) = \<sigma> (\<tau> t)"
         proof (intro C.join_eqI)
           show 1: "C.prfx (\<sigma> (\<tau> a)) (\<sigma> (\<tau> t))"
             by (simp add: A.source_is_prfx \<sigma>.preserves_prfx \<tau>.preserves_prfx t)
           show 2: "C.prfx (F (H t)) (\<sigma> (\<tau> t))"
             using t
             by (metis "1" B.arr_resid_iff_con B.composite_ofE B.ide_implies_arr
                 C.not_con_null(2) C.prfx_implies_con \<open>\<not> A.arr t \<Longrightarrow> (\<sigma> \<circ> \<tau>) t = C.null\<close>
                 \<sigma>.G.preserves_ide \<sigma>.general_naturality(2) \<tau>.naturality1' comp_apply)
           show 3: "\<sigma> (\<tau> t) \\\<^sub>C F (H t) = \<sigma> (\<tau> a) \\\<^sub>C F (H t)"
             by (metis (no_types, opaque_lifting) "1" A.arrE A.con_sym A.in_sourcesE
                 A.resid_arr_self A.src_congI C.not_ide_null C.null_is_zero(2)
                 \<open>\<not> A.arr t \<Longrightarrow> (\<sigma> \<circ> \<tau>) t = C.null\<close> \<sigma>.general_naturality(1) \<tau>.general_naturality(1)
                 \<tau>.naturality1 \<tau>.preserves_con(2) \<tau>.respects_cong_ide comp_eq_dest_lhs t)
           show "\<sigma> (\<tau> t) \\\<^sub>C \<sigma> (\<tau> a) = F (H t) \\\<^sub>C \<sigma> (\<tau> a)"
             (*
              * using t 1 2 3 C.apex_arr_prfx(1) C.apex_sym C.cube C.extensionality C.ideE C.trg_def
              * by (smt (verit, del_insts))
              *)
           proof -
             have "\<sigma> (\<tau> t) \\\<^sub>C \<sigma> (\<tau> a) =
                   (\<sigma> (\<tau> a) \<squnion>\<^sub>C F (H t)) \\\<^sub>C \<sigma> (\<tau> a)"
             proof -
               have "\<sigma> (\<tau> t) = \<sigma> (\<tau> a) \<squnion>\<^sub>C F (H t)"
                 by (metis "2" "3" C.comp_eqI C.composable_iff_comp_not_null C.join_def
                     C.join_expansion(1) C.join_sym C.joinable_iff_composable)
               thus ?thesis by argo
             qed
             also have "... = F (H t) \\\<^sub>C \<sigma> (\<tau> a)"
               by (metis "1" C.arr_prfx_join_self C.comp_eqI C.comp_resid_prfx
                   C.con_sym_ax C.join_def C.join_expansion(1) C.null_is_zero(2)
                   \<sigma>.extensionality \<sigma>.preserves_arr calculation)
             finally show ?thesis by blast
           qed
         qed
         thus ?thesis
           using t
           by (metis A.con_implies_arr(1) A.in_sourcesE C.join_is_join_of
               C.joinable_iff_join_not_null C.not_arr_null \<sigma>.preserves_arr \<tau>.preserves_arr
               comp_apply)
       qed
     qed
   qed

end
