section\<open>Kneser's Theorem and the Cauchy--Davenport Theorem: main proofs\<close>

(*
  Session: Kneser_Cauchy_Davenport
  Title:   Kneser_Cauchy_Davenport_main_proofs.thy
  Authors: Mantas Bakšys and Angeliki Koutsoukou-Argyraki, University of Cambridge.
  Date: September 2022
*)

theory Kneser_Cauchy_Davenport_main_proofs
  imports 
  Kneser_Cauchy_Davenport_preliminaries

begin

context additive_abelian_group

begin

subsection\<open>Proof of Kneser's Theorem\<close>

text\<open>The proof we formalise follows the paper \cite{DeVos_Kneser}. This version of Kneser's Theorem 
corresponds to Theorem 3.2 in \cite{Ruzsa_book}, or to Theorem 4.3 in \cite{Nathanson_book}.  \<close>

theorem Kneser:
  assumes "A \<subseteq> G" and "B \<subseteq> G" and "finite A" and "finite B" and hAne: "A \<noteq> {}" and hBne: "B \<noteq> {}"
  shows "card (sumset A B) \<ge>  card (sumset A (stabilizer (sumset A B))) + 
    card (sumset B (stabilizer (sumset A B))) - card (stabilizer (sumset A B))"
proof-
  have "\<And> n A B. additive_abelian_group G (\<oplus>) \<zero> \<Longrightarrow> A \<subseteq> G \<Longrightarrow> B \<subseteq> G \<Longrightarrow> 
    finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}  \<Longrightarrow> card (sumset A B) + card A = n \<Longrightarrow>
    card (sumset A B) \<ge>  card (sumset A (stabilizer (sumset A B))) + 
    card (sumset B (stabilizer (sumset A B))) - card ((stabilizer (sumset A B)))"
  proof-
    fix n
    show "\<And> A B. additive_abelian_group G (\<oplus>) \<zero> \<Longrightarrow> A \<subseteq> G \<Longrightarrow> B \<subseteq> G \<Longrightarrow> 
    finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}  \<Longrightarrow> card (sumset A B) + card A = n \<Longrightarrow>
    card (sumset A B) \<ge>  card (sumset A (stabilizer (sumset A B))) + 
    card (sumset B (stabilizer (sumset A B))) - card ((stabilizer (sumset A B)))"
    proof(induction n arbitrary : G "(\<oplus>)" \<zero> rule: nat_less_induct)
      fix n 
      fix A B G :: "'a set"
      fix add (infixl "[\<oplus>]" 65)
      fix zero ("[\<zero>]")
      assume hind: "\<forall>m<n. \<forall>x xa xb :: 'a set. \<forall> xc xd. 
        additive_abelian_group xb xc xd \<longrightarrow> x \<subseteq> xb \<longrightarrow>
        xa \<subseteq> xb \<longrightarrow> finite x \<longrightarrow> finite xa \<longrightarrow> x \<noteq> {} \<longrightarrow> xa \<noteq> {} \<longrightarrow>
        card (additive_abelian_group.sumset xb xc x xa) + card x = m \<longrightarrow>
        card (additive_abelian_group.sumset xb xc x (additive_abelian_group.stabilizer xb xc
        (additive_abelian_group.sumset xb xc x xa))) + card (additive_abelian_group.sumset xb xc xa
        (additive_abelian_group.stabilizer xb xc (additive_abelian_group.sumset xb xc x xa))) -
        card (additive_abelian_group.stabilizer xb xc (additive_abelian_group.sumset xb xc x xa))
        \<le> card (additive_abelian_group.sumset xb xc x xa)" and 
        hGroupG: "additive_abelian_group G ([\<oplus>]) [\<zero>]" and hAG: "A \<subseteq> G" and hBG: "B \<subseteq> G" and 
        hA: "finite A" and hB: "finite B" and hAne: "A \<noteq> {}" and hBne: "B \<noteq> {}" and
        hcardsum: "card (additive_abelian_group.sumset G ([\<oplus>]) A B) + card A = n"
      interpret G: additive_abelian_group G "([\<oplus>])" "[\<zero>]" using hGroupG by simp
      have hindG: "\<forall>m<n. \<forall>C D. C \<subseteq> G \<longrightarrow>
        D \<subseteq> G \<longrightarrow> finite C \<longrightarrow> finite D \<longrightarrow> C \<noteq> {} \<longrightarrow> D \<noteq> {} \<longrightarrow>
        card (G.sumset C D) + card C = m \<longrightarrow>
        card (G.sumset C (G.stabilizer
        (G.sumset C D))) + card (G.sumset D
        (G.stabilizer (G.sumset C D))) -
        card (G.stabilizer (G.sumset C D))
        \<le> card (G.sumset C D)" using hind hGroupG by blast
      show "card (G.sumset A (G.stabilizer (G.sumset A B))) + 
        card (G.sumset B (G.stabilizer (G.sumset A B))) - 
        card (G.stabilizer (G.sumset A B)) \<le> card (G.sumset A B)"
      proof(cases "G.stabilizer (G.sumset A B) = {[\<zero>]}")
        case hstab0: True
        show ?thesis
        proof (cases "card A = 1")
          case True
          then obtain a where "A = {a}" and "a \<in> G"
            by (metis hAG card_1_singletonE insert_subset)
          then show ?thesis using G.card_sumset_singleton_subset_eq 
            G.stabilizer_left_sumset_invariant G.stabilizer_subset_group G.sumset_commute 
            G.sumset_stabilizer_eq_self hBG by (metis diff_add_inverse eq_imp_le)
        next
          case False
          then have "card A \<ge> 2" using Suc_1 order_antisym_conv
            by (metis Suc_eq_plus1 bot.extremum card_seteq hA hAne le_add2 not_less_eq_eq)
          then obtain a a' where haA: "{a', a} \<subseteq> A" and hanot: "a' \<noteq> a" and ha1G: "a \<in> G" and 
            ha2G: "a' \<in> G"
            by (smt (verit, ccfv_threshold) card_2_iff hAG insert_subset 
                obtain_subset_with_card_n subset_trans)
          then have "(a' [\<oplus>] (G.inverse a)) \<notin> G.stabilizer B" using G.stabilizer_sub_sumset_right 
            hstab0 subset_singletonD by (metis G.commutative G.inverse_closed 
            G.invertible G.invertible_right_inverse2 G.right_unit empty_iff insert_iff)
          then obtain b where hb: "b \<in> B" and "(a' [\<oplus>] (G.inverse a)) [\<oplus>] b \<notin> B" 
            using G.stabilizer_def G.not_mem_stabilizer_obtain hBG hB hBne ha1G ha2G 
            G.composition_closed G.inverse_closed by (metis (no_types, lifting))
          then have habG: "a' [\<oplus>] b [\<oplus>] G.inverse a \<notin> B" 
            using hb hBG ha1G ha2G by (metis G.associative G.commutative G.inverse_closed subset_iff)
          have hbG: "b \<in> G" using hb hBG by auto
          let ?B' = "G.sumset (G.differenceset B {b}) {a}"
          have hB': "finite ?B'" using hB
            by (simp add: G.finite_minusset G.finite_sumset)
          have hB'G: "?B' \<subseteq> G" using G.sumset_subset_carrier by blast
          have hB'ne: "?B' \<noteq> {}" using hBne hbG ha1G sumset_is_empty_iff hBG by auto
          have hstabeq: "G.stabilizer (G.sumset A B) = G.stabilizer (G.sumset A ?B')" 
            using hbG ha1G hAG hBG G.stabilizer_unchanged by blast 
          have hstab0': "G.stabilizer (G.sumset A ?B') = {[\<zero>]}" using hstab0 hstabeq by blast
          have ha1B': "a \<in> ?B'"
          proof-
            have "(b [\<oplus>] G.inverse b) [\<oplus>] a \<in> ?B'" using hBG hbG ha1G hb G.minusset.minussetI by blast
            thus "a \<in> ?B'" by (simp add: hbG ha1G)
          qed
          then have hinter_nempty: "A \<inter> ?B' \<noteq> {}" using ha1B' haA by blast
          have ha2B': "a' \<notin> ?B'" 
          proof-
            have h1: "(a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b \<notin> G.differenceset B {b}"
            proof
              assume "(a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b \<in> G.differenceset B {b}"
              then obtain b' where "(a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b = b' [\<oplus>] G.inverse b" 
                and "b' \<in> B" using hbG G.minusset.simps G.sumset.cases by force
              then have "(a' [\<oplus>] b [\<oplus>] G.inverse a) \<in> B" using hbG
                by (smt (verit) G.composition_closed hBG ha1G ha2G G.inverse_closed G.invertible 
                    G.invertible_right_cancel subsetD)
              thus "False" using habG by auto
            qed
            have "((a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b) [\<oplus>] a \<notin> ?B'" 
            proof
              assume "((a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b) [\<oplus>] a \<in> ?B'"
              then obtain b' where "((a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b) [\<oplus>] a = b' [\<oplus>] a" 
                and "b' \<in> G.differenceset B {b}" using ha1G G.sumset.simps by auto
              then have "((a' [\<oplus>] b [\<oplus>] G.inverse a) [\<oplus>] G.inverse b) \<in> G.differenceset B {b}" 
                using ha1G by (smt (z3) G.sumset.simps G.additive_abelian_group_axioms 
                    G.composition_closed ha2G hbG G.inverse_closed G.invertible G.invertible_right_cancel)
              thus "False" using h1 by auto
            qed
            thus "a' \<notin> ?B'" using ha1G hbG
              by (smt (verit, del_insts) G.associative G.commutative G.composition_closed ha2G 
                  G.inverse_closed G.invertible G.invertible_left_inverse G.right_unit)
          qed
          have hinterA: "A \<inter> ?B' \<noteq> A" using haA ha2B' by auto
          have hintercard0: "0 < card (A \<inter> ?B')"   
            using hA hB hinter_nempty card_gt_0_iff by blast
          have hintercardA: "card (A \<inter> ?B') < card A" using hA hB hinterA card_mono
            by (simp add: psubsetI psubset_card_mono)
          have inj: "inj_on (\<lambda> x. x [\<oplus>] G.inverse b [\<oplus>] a) G" using inj_onI ha1G hb G.invertible 
              G.inverse_closed G.composition_closed by (smt (verit) G.invertible_right_cancel hbG)
          have 1: "card (G.sumset A B) = card (G.sumset A ?B')"
            using G.card_differenceset_singleton_mem_eq G.card_sumset_singleton_subset_eq hAG hB'G 
              ha1G hbG G.sumset_assoc G.sumset_commute G.sumset_subset_carrier
            by (smt (verit, del_insts))
          obtain C where hCconv: "G.convergent C A ?B'" and hCmin: "\<And> Y. Y \<in> G.convergent_set A ?B' 
            \<Longrightarrow> card (G.stabilizer Y) \<ge> card (G.stabilizer C)" 
            using G.exists_convergent_min_stabilizer[of n A ?B']
              hindG hA hB' hAG hB'G hinter_nempty hAne hcardsum hintercardA 1 hGroupG by auto
          have hC: "C \<subseteq> G.sumset A ?B'" and hCne: "C \<noteq> {}" and
            hCcard: "card C + card (G.stabilizer C) \<ge> 
            card (A \<inter> ?B') + card (G.sumset (A \<union> ?B') (G.stabilizer C))"
            using G.convergent_def hCconv by auto 
          then have hCfinite: "finite C" using hC G.finite_sumset hA hB'
            by (meson finite_subset)
          have htranslate: "card (G.sumset A {[\<zero>]}) + card (G.sumset ?B' {[\<zero>]}) - card {[\<zero>]} \<le> 
            card (G.sumset A ?B')"
          proof(cases "G.stabilizer C = {[\<zero>]}")
            case hCstab0: True
            have "card (G.sumset A {[\<zero>]}) + card (G.sumset ?B' {[\<zero>]}) - card {[\<zero>]} = card A + card ?B' -
              card {[\<zero>]}" using hAG hB'G G.card_minusset' by fastforce
            also have "... = card (A \<inter> ?B') + card (A \<union> ?B') - card {[\<zero>]}" 
              using hA hB' card_Un_Int by fastforce
            also have "... = card (A \<inter> ?B') + card (G.sumset (A \<union> ?B') {[\<zero>]}) - card {[\<zero>]}"
              by (simp add: Int_absorb1 Int_commute hAG G.sumset_subset_carrier)
            also have "... \<le> card C" using hCcard hCstab0 by auto
            also have "... \<le> card (G.sumset A ?B')" 
            using hC card_mono G.finite_sumset hA hB' by metis
            finally show ?thesis by simp
          next
            case hCstab_ne0: False
            have hCG: "C \<subseteq> G" using hC by (meson subset_trans G.sumset_subset_carrier)
            then have hstabC: "finite (G.stabilizer C)" using G.stabilizer_finite hCne hC 
              G.finite_sumset hA hB' by (metis Nat.add_0_right add_leE card.infinite hCcard 
              hintercard0 le_0_eq not_gr0)
            then have hcardstabC_gt_1: "card (G.stabilizer C) > 1" using G.zero_mem_stabilizer
              hCstab_ne0 hCG by (metis card_1_singletonE card_gt_0_iff diffs0_imp_equal empty_iff 
              gr_zeroI insertE less_one zero_less_diff)
            have "G.sumset (G.stabilizer C) (G.sumset A ?B') \<noteq> G.sumset A ?B'"
               using G.finite_sumset G.stabilizer_is_nonempty G.stabilizer_subset_group
               G.sumset_eq_sub_stabilizer G.sumset_subset_carrier hA hB' hCstab_ne0 hstab0'
               subset_singletonD by metis
            moreover have "card (G.sumset (G.stabilizer C) (G.sumset A ?B')) \<ge> card (G.sumset A ?B')"
              using G.card_le_sumset G.finite_sumset hA hB' hstabC
              by (meson hCG G.sumset_subset_carrier G.unit_closed G.zero_mem_stabilizer)
            ultimately have "\<not> G.sumset (G.stabilizer C) (G.sumset A ?B') \<subseteq> G.sumset A ?B'"
              using G.finite_sumset hA hB' card_seteq by metis
            then obtain x where hx1: "x \<in> G.sumset (G.stabilizer C) (G.sumset A ?B')" and 
              hx2: "x \<notin> G.sumset A ?B'" by auto
            then obtain a1 b1 c where "x = c [\<oplus>] (a1 [\<oplus>] b1)" and "c \<in> G.stabilizer C" and 
              ha1A: "a1 \<in> A" and hb1B': "b1 \<in> ?B'" and ha1memG: "a1 \<in> G" and hb1memG: "b1 \<in> G" 
              by (metis (no_types, lifting) G.sumset.cases)
            then have hx: "x \<in> G.sumset (G.stabilizer C) {a1 [\<oplus>] b1}" 
              using hx1 by (meson G.composition_closed hAG hB'G insertI1 G.stabilizer_subset_group 
              subsetD G.sumset.sumsetI)
            then have hnotsubAB: "\<not> G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) \<subseteq> G.sumset A ?B'" 
              using hx2 G.sumset_commute by auto
            let ?A1 = "A \<inter> (G.sumset {a1} (G.stabilizer C))"
            let ?A2 = "A \<inter> (G.sumset {b1} (G.stabilizer C))"
            let ?B1 = "?B' \<inter> (G.sumset {b1} (G.stabilizer C))"
            let ?B2 = "?B' \<inter> (G.sumset {a1} (G.stabilizer C))"
            let ?C1 = "C \<union> (G.sumset ?A1 ?B1)"
            let ?C2 = "C \<union> (G.sumset ?A2 ?B2)"
            let ?H1 = "G.stabilizer (G.sumset ?A1 ?B1)"
            let ?H2 = "G.stabilizer (G.sumset ?A2 ?B2)"
            have hA1ne: "?A1 \<noteq> {}" using ha1A G.zero_mem_stabilizer hCG
              by (metis (full_types) disjoint_iff_not_equal hAG insertCI G.right_unit subset_eq 
                G.sumset.sumsetI G.unit_closed)
            have hB1ne: "?B1 \<noteq> {}" using hb1B' G.zero_mem_stabilizer hCG
              by (metis G.composition_closed disjoint_iff_not_equal insertCI G.left_unit 
                  G.sumset.cases G.sumset.sumsetI G.sumset_commute G.unit_closed)
            have hnotsubC: "\<not> G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) \<subseteq> C" using hnotsubAB hC by blast
            have habstabempty: "G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) \<inter> C = {}"
            proof(rule ccontr)
              assume "G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) \<inter> C \<noteq> {}"
              then obtain z where 
                hz: "G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) \<inter> G.sumset {z} (G.stabilizer C) \<noteq> {}" and 
                hzC: "z \<in> C"   using G.stabilizer_coset_Un hCG by blast 
              then have "G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) = G.sumset {z} (G.stabilizer C)" using hz 
                G.sumset_stabilizer_eq_iff hCG G.sumset.simps hx by auto
              then have "G.sumset {a1 [\<oplus>] b1} (G.stabilizer C) \<subseteq> C" using hzC 
                by (simp add: hCG G.stabilizer_coset_subset)
              thus "False" using hnotsubC by simp
            qed
            have hA1B1sub: "G.sumset ?A1 ?B1 \<subseteq> G.sumset {a1 [\<oplus>] b1} (G.stabilizer C)" and 
              hB2A2sub: "G.sumset ?B2 ?A2 \<subseteq> G.sumset {a1 [\<oplus>] b1} (G.stabilizer C)"
              using G.sumset_Inter_subset_sumset ha1memG hb1memG by auto
            then have hA1B1Cempty: "G.sumset ?A1 ?B1 \<inter> C = {}" using habstabempty by blast
            then have hcardC1: "card ?C1 = card C + card (G.sumset ?A1 ?B1)" using card_Un_disjoint 
              G.finite_sumset hA hB' finite_Int hC finite_subset Int_commute by metis
            have hA1B1cardless: "card (G.sumset ?A1 ?B1) < card (G.sumset A B)"
            proof-
              have "G.sumset ?A1 ?B1 \<subseteq> G.sumset A ?B'" using G.sumset_mono by auto
              moreover have "G.sumset ?A1 ?B1 \<noteq> G.sumset A ?B'" 
                using hA1B1Cempty hC hCne hA1B1sub by auto
              ultimately show "card (G.sumset ?A1 ?B1) < card (G.sumset A B)" 
                  using G.finite_sumset hA hB' psubset_card_mono psubset_eq 1 by metis
            qed
            have hB2A2Cempty: "G.sumset ?B2 ?A2 \<inter> C = {}" using habstabempty hB2A2sub by blast
            then have hcardC2: "card ?C2 = card C + card (G.sumset ?B2 ?A2)" using card_Un_disjoint 
              G.finite_sumset hA hB' finite_Int hC finite_subset Int_commute G.sumset_commute by metis
            have hA2B2cardless: "card (G.sumset ?A2 ?B2) < card (G.sumset A B)"
            proof-
              have "G.sumset ?A2 ?B2 \<subset> G.sumset A ?B'" 
                using G.sumset_mono hB2A2Cempty hC hCne hB2A2sub G.sumset_commute psubset_eq
                by (metis Int_absorb1 Int_lower1)
              then show ?thesis by (simp add: 1 G.finite_sumset hA hB' psubset_card_mono)
            qed
            have "card ?A1 \<le> card A" using card_mono hA by (metis Int_lower1)
            then have "card (G.sumset ?A1 ?B1) + card ?A1 < card (G.sumset A B) + card A" 
              using hA1B1cardless by linarith
            then obtain l where hln: "l < n" and hind1: "card (G.sumset ?A1 ?B1) + card ?A1 = l" 
              using hcardsum by auto
            have "card ?A2 \<le> card A" using card_mono hA Int_lower1 by metis
            then have "card (G.sumset ?A2 ?B2) + card ?A2 < card (G.sumset A B) + card A"
              using hA2B2cardless by linarith
            then obtain k where hkn: "k < n" and hind2: "card (G.sumset ?A2 ?B2) + card ?A2 = k"
                using hcardsum by auto
            have hH1stabC: "?H1 \<subset> G.stabilizer C" using G.stabilizer_sumset_psubset_stabilizer 
                hA1ne hB1ne ha1memG hb1memG hnotsubAB by presburger
            then have "card ?H1 < card (G.stabilizer C)" using psubset_card_mono hstabC by auto
            moreover have hC1H1: "?H1 = G.stabilizer ?C1" using G.stabilizer_eq_stabilizer_union
              by (metis Int_commute hA hA1B1Cempty hA1ne hB' hB1ne hC hCfinite hCne ha1memG hb1memG hnotsubAB)
            ultimately have hC1notconv: "\<not> G.convergent ?C1 A ?B'" using hCmin G.convergent_set_def
              le_antisym less_imp_le_nat less_not_refl2 by fastforce
            have hC1ne: "?C1 \<noteq> {}" and hC2ne: "?C2 \<noteq> {}" using hCne by auto
            have hC1AB': "?C1 \<subseteq> G.sumset A ?B'" and hC2AB': "?C2 \<subseteq> G.sumset A ?B'" using hC 
              by (auto simp add: G.sumset_mono)
            have hA1G: "?A1 \<subseteq> G" and hA1 : "finite ?A1" and hB1G: "?B1 \<subseteq> G" and hB1: "finite ?B1" 
              using hAG hB'G hA hB' finite_Int by auto
            then have hindA1B1: "card (G.sumset ?A1 ?H1) + card (G.sumset ?B1 ?H1) - card ?H1 \<le> 
              card (G.sumset ?A1 ?B1)" using hindG hGroupG hA1ne hB1ne hind1 hln hAG hB'G 
              hA hB' by metis
            have hC1notconv_ineq: 
              "(int (card ?C1) + card ?H1 - card (A \<inter> ?B')) < int (card (G.sumset (A \<union> ?B') ?H1))" 
              using hC1notconv hC1ne hC1AB' hC1H1 G.convergent_def by auto
            have "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - card (G.sumset (A \<union> ?B') ?H1)
            \<le> (int (card C) + card (G.stabilizer C) - card (A \<inter> ?B')) - card (G.sumset (A \<union> ?B') ?H1)" 
            using hCcard by linarith
            then have "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - card (G.sumset (A \<union> ?B') ?H1) <
              (int (card C) + card (G.stabilizer C) - card (A \<inter> ?B')) - 
              (int (card ?C1) + card ?H1 - card (A \<inter> ?B'))" using hC1notconv_ineq by linarith
            also have "... = int (card (G.stabilizer C)) - card ?H1 - card (G.sumset ?A1 ?B1)" 
              using hcardC1 by presburger
            also have "... \<le> int (card (G.stabilizer C)) - card (G.sumset ?A1 ?H1) - card (G.sumset ?B1 ?H1)"
              using hindA1B1 by linarith
            text\<open> Finally, we deduce the inequality that is referred to as
     inequality (1) in \cite{DeVos_Kneser} for @{term ?A1} and  @{term ?B1}. \<close>
            finally have hA1B1ineq: "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - 
              card (G.sumset (A \<union> ?B') ?H1) < int (card (G.stabilizer C)) - 
              card (G.sumset ?A1 ?H1) - card (G.sumset ?B1 ?H1)" by simp
            have hB2ne: "?B2 \<noteq> {}" using G.sumset_inter_ineq hA1B1ineq ha1A ha1G hA hB' hAne hB'ne 
              hstabC hH1stabC ha1memG of_nat_0_le_iff by (smt (verit, del_insts))
            have hA2ne: "?A2 \<noteq> {}" using G.sumset_inter_ineq[of "A" "b1" "C" "?B'" "a1"] hA1B1ineq 
              hb1B' hb1memG hA hB' hAne hB'ne  hstabC hH1stabC of_nat_0_le_iff G.sumset_commute Un_commute by (smt (verit, ccfv_SIG))
            have hH2stabC: "?H2 \<subset> G.stabilizer C" using G.stabilizer_sumset_psubset_stabilizer 
              G.commutative hA2ne hB2ne ha1memG hb1memG hnotsubAB by presburger
            then have "card ?H2 < card (G.stabilizer C)" using psubset_card_mono hstabC by auto
            moreover have hC2H2: "?H2 = G.stabilizer ?C2" using G.stabilizer_eq_stabilizer_union
              by (smt (verit, ccfv_threshold) G.sumset_commute Int_commute hA hA2ne hB' hB2A2Cempty
                hB2ne hC hCfinite hCne ha1memG hb1memG hnotsubAB)
            ultimately have hC2notconv: "\<not> G.convergent ?C2 A ?B'" 
              using hCmin G.convergent_set_def le_antisym less_imp_le_nat less_not_refl2 
              by fastforce
            have hA2G: "?A2 \<subseteq> G" and hA2 : "finite ?A2" and hB2G: "?B2 \<subseteq> G" and hB2: "finite ?B2" 
              using hAG hB'G hA hB' finite_Int by auto
            then have hindA2B2: "card (G.sumset ?A2 ?H2) + card (G.sumset ?B2 ?H2) - card ?H2 \<le> 
              card (G.sumset ?A2 ?B2)"
              using hindG hGroupG hA2ne hB2ne hind2 hkn hAG hB'G hA hB' by metis
            have hC2notconv_ineq: 
              "(int (card ?C2) + card ?H2 - card (A \<inter> ?B')) < int (card (G.sumset (A \<union> ?B') ?H2))" 
              using hC2notconv hC2ne hC2AB' hC2H2 G.convergent_def by auto
            have "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - card (G.sumset (A \<union> ?B') ?H2)
              \<le> (int (card C) + card (G.stabilizer C) - card (A \<inter> ?B')) - card (G.sumset (A \<union> ?B') ?H2)" 
              using hCcard by linarith
            then have "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - card (G.sumset (A \<union> ?B') ?H2) <
              (int (card C) + card (G.stabilizer C) - card (A \<inter> ?B')) - 
              (int (card ?C2) + card ?H2 - card (A \<inter> ?B'))" using hC2notconv_ineq by linarith
            also have "... = int (card (G.stabilizer C)) - card ?H2 - card (G.sumset ?A2 ?B2)" 
              using hcardC2 G.sumset_commute by simp
            also have "... \<le> int (card (G.stabilizer C)) - card (G.sumset ?A2 ?H2) - card (G.sumset ?B2 ?H2)"
              using hindA2B2 by linarith
            
            text\<open> Analogously, we deduce the inequality that is referred to as
     inequality (1) in \cite{DeVos_Kneser} for @{term ?A2} and  @{term ?B2}. \<close>
           
            finally have hA2B2ineq: "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - 
              card (G.sumset (A \<union> ?B') ?H2) < int (card (G.stabilizer C)) - 
              card (G.sumset ?A2 ?H2) - card (G.sumset ?B2 ?H2)" by simp
            have hfinsumH2:"finite (G.sumset (A \<union> ?B') ?H2)" 
              using G.finite_sumset hA hB' finite_UnI hstabC hH2stabC finite_subset psubset_imp_subset
              by metis
            have hsubsumH2: "G.sumset (A \<union> ?B') ?H2 \<subseteq> G.sumset (A \<union> ?B') (G.stabilizer C)" 
              using G.sumset.cases hAG hB'G G.stabilizer_subset_group hH2stabC psubset_imp_subset
              by (smt (verit, best) subset_Un_eq G.sumset_commute G.sumset_subset_Un1)
            then have hsumH2card_le: "card (G.sumset (A \<union> ?B') ?H2) \<le> 
              card (G.sumset (A \<union> ?B') (G.stabilizer C))"
              using card_mono G.finite_sumset G.stabilizer_finite hC hCne hCG hA hB'
              by (metis finite_UnI hstabC)
            have hfinsumH1: "finite (G.sumset (A \<union> ?B') ?H1)" 
              using finite_sumset finite_Un psubsetE by (metis G.finite_sumset G.stabilizer_finite 
                G.sumset_subset_carrier Int_Un_eq(4) hA hA1 hB' hB1 hC1H1 hH1stabC habstabempty)
            have hsubsumH1: "G.sumset (A \<union> ?B') ?H1 \<subseteq> G.sumset (A \<union> ?B') (G.stabilizer C)" 
              using G.sumset.cases psubsetE subset_refl G.sumset_mono hH1stabC by simp
            have hsumH1card_le: "card (G.sumset (A \<union> ?B') ?H1) \<le> card (G.sumset (A \<union> ?B') (G.stabilizer C))"
              using card_mono G.finite_sumset G.stabilizer_finite by (metis finite_UnI hA hB' hstabC hsubsumH1)
            have ha1b1stabCne: "G.sumset {a1} (G.stabilizer C) \<noteq> G.sumset {b1} (G.stabilizer C)"
            proof
              assume ha1b1: "G.sumset {a1} (G.stabilizer C) = G.sumset {b1} (G.stabilizer C)"
              have hfin: "finite (G.sumset ?A1 ?H1 \<union> G.sumset ?B1 ?H1)" 
                using finite_UnI G.finite_sumset hA1 hB1 hH1stabC hstabC psubset_imp_subset
                by (metis finite_subset)
              have "int (card (G.sumset {a1} (G.stabilizer C))) - card (G.sumset ?A1 ?H1) - 
                card (G.sumset ?B1 ?H1) \<le> int (card (G.sumset {a1} (G.stabilizer C))) - 
                card (G.sumset ?A1 ?H1 \<union> G.sumset ?B1 ?H1)"
                using card_Un_le[of "G.sumset ?A1 ?H1" "G.sumset ?B1 ?H1"] by linarith
              also have "... \<le> card (G.sumset {a1} (G.stabilizer C) - (G.sumset ?A1 ?H1 \<union> G.sumset ?B1 ?H1))"
                using diff_card_le_card_Diff[of "G.sumset ?A1 ?H1 \<union> G.sumset ?B1 ?H1" 
                  "G.sumset {a1} (G.stabilizer C)"] hfin by linarith
              also have "... \<le> card (G.sumset {a1} (G.stabilizer C) - G.sumset (?A1 \<union> ?B1) ?H1)"
                using G.sumset_subset_Un1 by auto
              also have "... \<le> card (G.sumset (A \<union> ?B') (G.stabilizer C) - G.sumset (A \<union> ?B') ?H1)"
              proof-
                have hsub: "G.sumset {a1} (G.stabilizer C) - G.sumset (?A1 \<union> ?B1) ?H1 \<subseteq> 
                  G.sumset (A \<union> ?B') (G.stabilizer C) - G.sumset (A \<union> ?B') ?H1"
                proof
                  fix x assume hx: "x \<in> G.sumset {a1} (G.stabilizer C) - G.sumset (?A1 \<union> ?B1) ?H1"
                  then obtain c where hxac: "x = a1 [\<oplus>] c" and hc: "c \<in> G.stabilizer C" 
                    using G.sumset.cases by blast
                  then have "x \<in> G.sumset (A \<union> ?B') (G.stabilizer C)" using ha1A hAG 
                    G.stabilizer_subset_group by (simp add: subset_iff G.sumset.sumsetI)
                  moreover have "x \<notin> G.sumset (A \<union> ?B') ?H1"
                  proof
                    assume hx1: "x \<in> G.sumset (A \<union> ?B') ?H1"
                    then obtain y h1 where hxy: "x = y [\<oplus>] h1" and hy: "y \<in> A \<union> ?B'" and 
                      hh1: "h1 \<in> ?H1" using G.sumset.cases by blast
                    then have hyG: "y \<in> G" and hcG: "c \<in> G" and hh1G: "h1 \<in> G" 
                      using hAG hB'G G.stabilizer_subset_group hc by auto
                    then have "y = a1 [\<oplus>] (c [\<oplus>] G.inverse h1)" using hxac hxy ha1A hAG 
                      by (metis G.associative G.commutative G.composition_closed in_mono 
                        G.inverse_closed G.invertible G.invertible_left_inverse2)
                    moreover have "h1 \<in> G.stabilizer C" using hh1 hH1stabC by auto
                    moreover hence "c [\<oplus>] G.inverse h1 \<in> G.stabilizer C" using hc
                        G.stabilizer_is_subgroup subgroup_def G.group_axioms
                        group.invertible subgroup.subgroup_inverse_iff 
                        submonoid.sub_composition_closed hh1G by metis
                    ultimately have "y \<in> G.sumset {a1} (G.stabilizer C)" using ha1G hcG hAG ha1A hh1G
                      by blast
                    then have "y \<in> ?A1 \<union> ?B1" using hy  by (simp add: ha1b1)
                    thus "False" using hx hxy hh1 hh1G hyG by auto
                  qed
                  ultimately show "x \<in> G.sumset (A \<union> ?B') (G.stabilizer C) - G.sumset (A \<union> ?B') ?H1" by simp
                qed
                moreover have "finite (G.sumset {a1} (G.stabilizer C) - G.sumset (?A1 \<union> ?B1) ?H1)"
                  using finite_subset G.finite_sumset hstabC by simp
                moreover hence "finite (G.sumset (A \<union> ?B') (G.stabilizer C) - G.sumset (A \<union> ?B') ?H1)"
                  using finite_subset G.finite_sumset hstabC hA hB' finite_UnI by simp
                moreover have "card (G.sumset {a1} (G.stabilizer C) - G.sumset (?A1 \<union> ?B1) ?H1) \<le> 
                  card (G.sumset (A \<union> ?B') (G.stabilizer C) - G.sumset (A \<union> ?B') ?H1)" 
                  using card_mono hsub calculation(3) by auto
                ultimately show ?thesis using card_Diff_subset by linarith
              qed
              also have "... = int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - card (G.sumset (A \<union> ?B') ?H1)"
                using card_Diff_subset[OF hfinsumH1 hsubsumH1] hsumH1card_le by linarith
              finally have "int (card (G.stabilizer C)) - card (G.sumset ?A1 ?H1) - card (G.sumset ?B1 ?H1)
                \<le> int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - card (G.sumset (A \<union> ?B') ?H1)"
                using hCG subset_iff G.card_sumset_singleton_subset_eq G.stabilizer_subset_group 
                hAG ha1A by auto
              thus "False" using hA1B1ineq by linarith
            qed
            have "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - 
              card (G.sumset (A \<union> ?B') ?H1) \<ge> 0" by (simp add: hsumH1card_le)
            then have "int (card (G.stabilizer C)) - 
              card (G.sumset ?A1 ?H1) - card (G.sumset ?B1 ?H1) > 0" using hA1B1ineq by linarith
            moreover have "int (card ?H1) dvd int (card (G.stabilizer C)) - 
              card (G.sumset ?A1 ?H1) - card (G.sumset ?B1 ?H1)" using 
              G.stabilizer_subset_stabilizer_dvd hH1stabC psubset_imp_subset int_dvd_int_iff dvd_diff
              G.card_stabilizer_divide_sumset[OF hA1G] G.card_stabilizer_divide_sumset[OF hB1G]
              by fastforce
            ultimately have "int (card (G.stabilizer C)) - 
              card (G.sumset ?A1 ?H1) - card (G.sumset ?B1 ?H1) \<ge> int (card ?H1)" 
              using zdvd_imp_le by blast
            moreover have hA1_le_sum: "card ?A1 \<le> card (G.sumset ?A1 ?H1)"
              using G.sumset_commute G.card_le_sumset G.zero_mem_stabilizer hA1G hA1 hH1stabC hstabC 
              by (metis finite_subset psubset_imp_subset G.unit_closed)
            moreover have hB1_le_sum: "card ?B1 \<le> card (G.sumset ?B1 ?H1)"
              using G.sumset_commute G.card_le_sumset G.zero_mem_stabilizer hB1G hB1 hH1stabC hstabC 
              by (metis finite_subset psubset_imp_subset G.unit_closed)
            
            text\<open> The above facts combined allow us to deduce the inequality that is referred to as
     inequality (2) in  \cite{DeVos_Kneser} for @{term ?A1},  @{term ?B1} and @{term ?H1}. \<close>
           
            ultimately have 21: "int (card (G.stabilizer C)) \<ge> int (card ?H1) + card ?A1 + card ?B1" 
              by linarith
            have "int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) - 
              card (G.sumset (A \<union> ?B') ?H2) \<ge> 0" by (simp add: hsumH2card_le)
            then have "int (card (G.stabilizer C)) - 
              card (G.sumset ?A2 ?H2) - card (G.sumset ?B2 ?H2) > 0" using hA2B2ineq by linarith
            moreover have "int (card ?H2) dvd int (card (G.stabilizer C)) - 
              card (G.sumset ?A2 ?H2) - card (G.sumset ?B2 ?H2)" using psubset_imp_subset
              G.stabilizer_subset_stabilizer_dvd hH2stabC int_dvd_int_iff dvd_diff
              G.card_stabilizer_divide_sumset[OF hA2G] G.card_stabilizer_divide_sumset[OF hB2G] 
              by fastforce
            ultimately have "int (card (G.stabilizer C)) - 
              card (G.sumset ?A2 ?H2) - card (G.sumset ?B2 ?H2) \<ge> int (card ?H2)" 
              using zdvd_imp_le by blast
            moreover have hA2_le_sum: "card ?A2 \<le> card (G.sumset ?A2 ?H2)"
              using G.sumset_commute G.card_le_sumset G.zero_mem_stabilizer G.stabilizer_subset_group 
                hA2G hA2 hH2stabC hstabC psubset_imp_subset by (metis finite_subset G.unit_closed)
            moreover have hB2_le_sum: "card ?B2 \<le> card (G.sumset ?B2 ?H2)"
              using G.sumset_commute G.card_le_sumset G.zero_mem_stabilizer G.stabilizer_subset_group 
                hB2G hB2 hH2stabC hstabC psubset_imp_subset by (metis finite_subset G.unit_closed)
     
 text\<open>Analogously, the above facts combined allow us to deduce the inequality that is referred to as
     inequality (2) in \cite{DeVos_Kneser} for @{term ?A2},  @{term ?B2} and @{term ?H2}. \<close>

            ultimately have 22: "int (card (G.stabilizer C)) \<ge> int (card ?H2) + card ?A2 + card ?B2" 
              by linarith
            let ?S = "G.sumset {a1} (G.stabilizer C) - (?A1 \<union> ?B2)"
            let ?T = "G.sumset {b1} (G.stabilizer C) - (?A2 \<union> ?B1)"
            have hS : "finite ?S" and hT: "finite ?T" using G.finite_sumset hstabC by auto
            have hST: "?S \<inter> ?T = {}" using ha1b1stabCne Diff_Int2 Diff_Int_distrib2 Int_Diff Int_Un_eq(4) 
              Int_absorb Int_commute Int_empty_right Int_insert_right Un_empty empty_Diff hA1ne 
              hA2ne G.sumset_commute G.sumset_is_empty_iff G.sumset_stabilizer_eq_iff
              by (smt (verit, ccfv_threshold) G.sumset_assoc)
            have hSTcard_le: "card ?S + card ?T + card (G.sumset (A \<union> ?B') {[\<zero>]}) \<le> 
                card (G.sumset (A \<union> ?B') (G.stabilizer C))" 
            proof-
              have "G.sumset {a1} (G.stabilizer C) \<subseteq> G.sumset (A \<union> ?B') (G.stabilizer C)" and 
                "G.sumset {b1} (G.stabilizer C) \<subseteq> G.sumset (A \<union> ?B') (G.stabilizer C)" 
                using G.sumset_mono ha1A hb1B' subset_refl empty_subsetI insert_subset by auto
              moreover have "(G.sumset (A \<union> ?B') {[\<zero>]}) \<subseteq> G.sumset (A \<union> ?B') (G.stabilizer C)"
                using G.sumset_mono subset_refl empty_subsetI insert_subset G.zero_mem_stabilizer 
                by metis
              ultimately have hsub: "?S \<union> ?T \<union> (G.sumset (A \<union> ?B') {[\<zero>]}) \<subseteq> 
                G.sumset (A \<union> ?B') (G.stabilizer C)" by blast
              have "?S \<inter> G.sumset (A \<union> ?B') {[\<zero>]} = {}" by auto
              moreover have "(?S \<union> ?T) \<inter> G.sumset (A \<union> ?B') {[\<zero>]} = {}" by auto
              ultimately have "card ?S + card ?T + card (G.sumset (A \<union> ?B') {[\<zero>]}) = 
                card (?S \<union> ?T \<union> (G.sumset (A \<union> ?B') {[\<zero>]}))" using card_Un_disjoint hS hT 
                G.finite_sumset finite_UnI hA hB' hST by (metis finite.emptyI finite.insertI)
              also have "... \<le> card (G.sumset (A \<union> ?B') (G.stabilizer C))" using card_mono 
                G.finite_sumset finite_UnI hA hB' hstabC hsub by metis 
              finally show ?thesis by simp
            qed
            have hAB_not_conv: "\<not> G.convergent (G.sumset A ?B') A ?B'" using hCmin hstab0 
                G.convergent_set_def hcardstabC_gt_1 hstab0' by fastforce
            then have "card (G.sumset A ?B') + card {[\<zero>]} < card (A \<inter> ?B') + 
              card (G.sumset (A \<union> ?B') {[\<zero>]})" using G.convergent_def hAne hB'ne hAG hB'G hstab0' 
              subset_refl by auto
            then have hAB'sum: "int (card (G.sumset (A \<union> ?B') {[\<zero>]})) + card (A \<inter> ?B') - 
              card (G.sumset A ?B') > 1" by simp
            moreover have "int (card ?A1) + card ?B1 \<le> int (card (G.sumset ?A1 ?H1)) + 
              card (G.sumset ?B1 ?H1)" using hA1_le_sum hB1_le_sum by linarith
            moreover hence "int (card ?A1) + card ?B1 - card ?H1 \<le> card (G.sumset ?A1 ?B1)" 
              using hindA1B1 by linarith
            ultimately have "int (card ?S) + card ?T + card ?A1 + card ?B1 - card ?H1 < 
              int (card ?S) + card ?T + card (G.sumset (A \<union> ?B') {[\<zero>]}) + card (A \<inter> ?B') - 
              card (G.sumset A ?B') + card (G.sumset ?A1 ?B1)" by linarith
            also have "... \<le> int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) + card (A \<inter> ?B') - card C"
            proof-
              have "G.sumset ?A1 ?B1 \<union> C \<subseteq> G.sumset A ?B'" using hC G.sumset_mono by auto
              then have "card (G.sumset ?A1 ?B1) + card C \<le> 
                card (G.sumset A ?B')" using card_Un_disjoint hCfinite G.finite_sumset hA1 hB1 hA1B1Cempty 
                  card_mono hA hB' by metis
              then show ?thesis using hSTcard_le by linarith
            qed

            text\<open>From this, inequality (3) \cite{DeVos_Kneser} follows for @{term ?A1},  
            @{term ?B1} and @{term ?H1}.\<close>

            finally have 31: "int (card ?S) + card ?T + card ?A1 + card ?B1 - card ?H1 < 
              card (G.stabilizer C)" using hCcard by linarith
            have "int (card ?A2) + card ?B2 \<le> int (card (G.sumset ?A2 ?H2)) + 
              card (G.sumset ?B2 ?H2)" using hA2_le_sum hB2_le_sum by linarith
            moreover hence "int (card ?A2) + card ?B2 - card ?H2 \<le> card (G.sumset ?A2 ?B2)" 
              using hindA2B2 by linarith
            ultimately have "int (card ?S) + card ?T + card ?A2 + card ?B2 - card ?H2 < 
              int (card ?S) + card ?T + card (G.sumset (A \<union> ?B') {[\<zero>]}) + card (A \<inter> ?B') - 
              card (G.sumset A ?B') + card (G.sumset ?A2 ?B2)" using hAB'sum by linarith
            also have "... \<le> int (card (G.sumset (A \<union> ?B') (G.stabilizer C))) + card (A \<inter> ?B') - card C"
            proof-
              have "G.sumset ?A2 ?B2 \<union> C \<subseteq> G.sumset A ?B'" using hC G.sumset_mono by auto
              then have "card (G.sumset ?A2 ?B2) + card C \<le> 
                card (G.sumset A ?B')" using card_Un_disjoint hCfinite G.finite_sumset hA2 hB2 hA1B1Cempty 
                  card_mono hA hB' hB2A2Cempty G.sumset_commute by metis
              then show ?thesis using hSTcard_le by linarith
            qed
 
            text\<open>From this, inequality (3) \cite{DeVos_Kneser} follows for @{term ?A2},
            @{term ?B2} and @{term ?H2}.\<close>

            finally have 32: "int (card ?S) + card ?T + card ?A2 + card ?B2 - card ?H2 < 
              card (G.stabilizer C)" using hCcard by linarith
            
            text\<open> Adding together the four inequalities obtained by versions of inequalities
               (2) and (3) and dividing by 2 gives the following inequality: \<close> 
            
            have 4: "2 * int (card (G.stabilizer C)) > int (card ?A1) + card ?B2 + card ?S + card ?T + card ?B1 + card ?A2"
              using 21 22 31 32 by linarith
            have "G.sumset {a1} (G.stabilizer C) = (?S \<union> ?A1) \<union> ?B2" and
              hb1T: "G.sumset {b1} (G.stabilizer C) = (?T \<union> ?A2) \<union> ?B1" by auto
            then have "card (G.stabilizer C) \<le> card ?S + card ?A1 + card ?B2"
              using card_Un_le[of "?S" "?A1"] card_Un_le[of "?S \<union> ?A1" "?B2"] 
                G.card_sumset_singleton_subset_eq G.stabilizer_subset_group ha1A hAG by auto
            moreover have "card (G.stabilizer C) \<le> card ?T + card ?A2 + card ?B1"
              using hb1T card_Un_le[of "?T" "?A2"] card_Un_le[of "?T \<union> ?A2" "?B1"]
              G.card_sumset_singleton_subset_eq G.stabilizer_subset_group hb1B' hB'G by auto
            
            text\<open> Combining the inequality labelled @{term 4} above with the above facts, the claim 
     follows:\<close>
            ultimately show ?thesis using 4 by linarith
          qed
   
          text\<open>It remains to transfer the statement of inequality labelled @{term 1} into an analogous 
       one, which replaces @{term ?B'} with @{term B}. \<close>

          have 2: "card (G.sumset A (G.stabilizer (G.sumset A B))) = 
            card (G.sumset A (G.stabilizer (G.sumset A ?B')))"
            using hstabeq by auto
          have 3: "card (G.sumset B (G.stabilizer (G.sumset A B))) = 
            card (G.sumset ?B' (G.stabilizer (G.sumset A ?B')))" using hstabeq hstab0' G.sumset_commute
            by (metis G.card_differenceset_singleton_mem_eq G.card_sumset_singleton_subset_eq 
            G.sumset_D(1) G.sumset_commute G.sumset_subset_carrier Int_absorb1 Int_commute hBG ha1G hbG)
          then show ?thesis using 1 2 3 hstabeq hstab0' htranslate by auto
        qed
      next
        case hstabne0: False
        let ?K = "G.stabilizer (G.sumset A B)"
        have hcardK_gt_1: "card ?K > 1" using G.stabilizer_finite G.sumset_subset_carrier G.finite_sumset 
          hA hB hstabne0 G.zero_mem_stabilizer by (metis card_0_eq card_1_singletonE G.card_sumset_0_iff 
          empty_iff hAG hAne hBG hBne insertE less_one linorder_neqE_nat)
        interpret K: subgroup_of_additive_abelian_group ?K G "([\<oplus>])" "[\<zero>]"
          using G.stabilizer_is_subgroup subgroup_of_additive_abelian_group_def 
          by (metis G.abelian_group_axioms G.group_axioms hGroupG subgroup_of_abelian_group_def 
            subgroup_of_group.intro)
        let ?\<phi> = "K.Class"
        have h\<phi>: "\<And> a. a \<in> G \<Longrightarrow> ?\<phi> a = (\<lambda> x. G.sumset {x} ?K) a" 
          using K.Left_Coset_Class_unit G.Left_Coset_eq_sumset_stabilizer by simp
        interpret GK: additive_abelian_group "G.Factor_Group G ?K" K.quotient_composition "K.Class [\<zero>]"
        proof
          fix x y assume "x \<in> K.Partition" and "y \<in> K.Partition"
          then obtain a b where "x = K.Class a" and "y = K.Class b" and "a \<in> G" and "b \<in> G" 
            by (meson K.representant_exists)
          then show "K.quotient_composition x y = K.quotient_composition y x"
            using K.Class_commutes_with_composition G.commutative by presburger
        qed
        have hGroupGK: "additive_abelian_group (G.Factor_Group G ?K) K.quotient_composition (K.Class [\<zero>])" ..
        
        text\<open>Here, we specialize the induction hypothesis to the factor group.\<close>

        let ?K_repr = "K.\<phi> ` K.Partition"
        have "\<And> x y. x \<in> ?K_repr \<Longrightarrow> y \<in> ?K_repr \<Longrightarrow> K.quot_comp_alt x y = K.quot_comp_alt y x"
          using K.quot_comp_alt_def G.commutative K.phi_image_subset subsetD by (metis (full_types))
        then interpret K_repr: additive_abelian_group ?K_repr K.quot_comp_alt "K.\<phi> ?K"
          using Group_Theory.group.axioms(1)[OF K.phi_image_group]
          by (auto simp add: additive_abelian_group_def abelian_group_def K.phi_image_group
            commutative_monoid_axioms_def commutative_monoid_def)
        have hindrepr: "\<And> m C D. m < n \<longrightarrow> C \<subseteq> ?K_repr \<longrightarrow> D \<subseteq> ?K_repr \<longrightarrow> finite C \<longrightarrow>
          finite D \<longrightarrow> C \<noteq> {} \<longrightarrow> D \<noteq> {} \<longrightarrow> card (K_repr.sumset C D) + card C = m \<longrightarrow> 
          card (K_repr.sumset C (K_repr.stabilizer (K_repr.sumset C D))) + 
          card (K_repr.sumset D (K_repr.stabilizer (K_repr.sumset C D))) - card (K_repr.stabilizer (K_repr.sumset C D)) \<le>
          card (K_repr.sumset C D)" using hind K_repr.additive_abelian_group_axioms by blast
        have hindfactor: "\<And> m C D. m < n \<longrightarrow>  C \<subseteq> K.Partition \<longrightarrow> D \<subseteq> K.Partition \<longrightarrow> finite C \<longrightarrow>
          finite D \<longrightarrow> C \<noteq> {} \<longrightarrow> D \<noteq> {} \<longrightarrow> card (GK.sumset C D) + card C = m \<longrightarrow> 
          card (GK.sumset C (GK.stabilizer (GK.sumset C D))) + 
          card (GK.sumset D (GK.stabilizer (GK.sumset C D))) - card (GK.stabilizer (GK.sumset C D)) \<le>
          card (GK.sumset C D)"
        proof(intro impI)
          fix m C D assume hmn: "m < n" and hCK: "C \<subseteq> K.Partition" and hDK: "D \<subseteq> K.Partition" and 
          hC: "finite C" and hD: "finite D" and hCne: "C \<noteq> {}" and hDne: "D \<noteq> {}" and 
          hCDcard: "card (GK.sumset C D) + card C = m"
          let ?C = "K.\<phi> ` C" and ?D = "K.\<phi> ` D"
          have hCrepr: "?C \<subseteq> ?K_repr" and hDrepr: "?D \<subseteq> ?K_repr" using hCK hDK by auto
          have hCfin: "finite ?C" and hDfin: "finite ?D" and hCne_1: "?C \<noteq> {}" and hDne_1: "?D \<noteq> {}" using hC hD hCne hDne by auto
          have hcardC: "card ?C = card C" using K.phi_inj_on hC card_image inj_on_subset hCK by metis
          have "card (GK.sumset C D) = card (K_repr.sumset ?C ?D)" 
            using card_image K.phi_inj_on inj_on_subset K.phi_image_sumset_eq 
              GK.sumset_subset_carrier hCK hDK by (smt (verit, best))
          then have "card (K_repr.sumset ?C ?D) + card ?C = m" using hCDcard hcardC by presburger
          then have "card (K_repr.sumset ?C (K_repr.stabilizer (K_repr.sumset ?C ?D))) + 
          card (K_repr.sumset ?D (K_repr.stabilizer (K_repr.sumset ?C ?D))) - card (K_repr.stabilizer (K_repr.sumset ?C ?D)) \<le>
          card (K_repr.sumset ?C ?D)" 
            using hindrepr hCfin hDfin hCne_1 hDne_1 hCrepr hDrepr hmn by blast
          then show "card (GK.sumset C (GK.stabilizer (GK.sumset C D))) + 
          card (GK.sumset D (GK.stabilizer (GK.sumset C D))) - card (GK.stabilizer (GK.sumset C D)) \<le>
          card (GK.sumset C D)" using K.phi_image_sumset_eq K.phi_image_stabilizer_eq
            K.phi_inj_on inj_on_subset hCK hDK card_image
            by (smt (z3) GK.stabilizer_subset_group GK.sumset_subset_carrier)
        qed
        have hstab0: "GK.stabilizer (?\<phi> ` (G.sumset A B)) = {K.Class [\<zero>]}"
        proof
          show "GK.stabilizer (?\<phi> ` G.sumset A B) \<subseteq> {K.Class [\<zero>]}"
          proof
            fix x assume hx: "x \<in> GK.stabilizer (?\<phi> ` G.sumset A B)"
            moreover have "?\<phi> ` G.sumset A B \<subseteq> K.Partition" 
              using K.natural.map_closed G.sumset_subset_carrier by blast
            ultimately have hsum: "GK.sumset {x} (?\<phi> ` G.sumset A B) = ?\<phi> ` G.sumset A B" 
              using GK.stabilizer_def by auto
            obtain x' where hx\<phi>: "x = ?\<phi> x'" and hx'G: "x' \<in> G" 
              using hx GK.stabilizer_subset_group K.representant_exists by force
            have hsumset: "GK.sumset {x} (?\<phi> ` G.sumset A B) = (\<lambda> a. ?\<phi> (x' [\<oplus>] a)) ` G.sumset A B"
            proof
              show "GK.sumset {x} (?\<phi> ` G.sumset A B) \<subseteq> (\<lambda>a. ?\<phi> (x' [\<oplus>] a)) ` G.sumset A B"
              proof
                fix y assume "y \<in> GK.sumset {x} (?\<phi> ` G.sumset A B)"
                then obtain z where "z \<in> G.sumset A B" and "y = K.quotient_composition (?\<phi> x') (?\<phi> z)" 
                  using GK.sumset.cases hx\<phi> by blast
                then show "y \<in> (\<lambda>a. ?\<phi> (x' [\<oplus>] a)) ` G.sumset A B" 
                  using K.Class_commutes_with_composition G.composition_closed hx'G G.sumset.cases 
                    imageI by metis
              qed
            next
              show "(\<lambda>a. ?\<phi> (x' [\<oplus>] a)) ` G.sumset A B \<subseteq> GK.sumset {x} (?\<phi> ` G.sumset A B)"
              proof
                fix y assume "y \<in> (\<lambda>a. ?\<phi> (x' [\<oplus>] a)) ` G.sumset A B"
                then obtain z where hz: "z \<in> G.sumset A B" and "y = ?\<phi> (x' [\<oplus>] z)" by blast
                then have "y = K.quotient_composition (?\<phi> x') (?\<phi> z)" using 
                    K.Class_commutes_with_composition G.composition_closed hx'G G.sumset.cases by metis
                then show "y \<in> GK.sumset {x} (?\<phi> ` G.sumset A B)" 
                  using hx\<phi> hz imageI hx GK.sumset.sumsetI K.natural.map_closed 
                  by (metis G.composition_closed hx'G insertCI G.sumset.cases)
              qed
            qed
            have "G.sumset {x'} (G.sumset A B) \<subseteq> G.sumset (G.sumset A B) ?K"
            proof
              fix y assume "y \<in> G.sumset {x'} (G.sumset A B)"
              then obtain z where hz: "z \<in> G.sumset A B" and hy: "y = x' [\<oplus>] z" using G.sumset.cases by blast
              then have "?\<phi> (x' [\<oplus>] z) \<in> ?\<phi> ` G.sumset A B" using hsum hsumset by blast
              then obtain w where hw: "{w} \<subseteq> G.sumset A B" and "w \<in> G.sumset A B" 
                and "?\<phi> (x' [\<oplus>] z) = ?\<phi> w" by auto
              then have "(x' [\<oplus>] z) \<in> G.differenceset (G.sumset {w} ?K) ?K" 
                using h\<phi> G.sumset_subset_carrier hx'G hz G.sumset_eq_subset_differenceset 
                  G.composition_closed G.stabilizer_is_nonempty G.stabilizer_subset_group G.sumset.cases 
                   K.Class_self G.differenceset_stabilizer_eq G.sumset_assoc by metis
              moreover have "G.differenceset (G.sumset {w} ?K) ?K \<subseteq> G.sumset {w} ?K" 
                using hw by (simp add: G.differenceset_stabilizer_eq G.sumset_assoc)
              ultimately show "y \<in> G.sumset (G.sumset A B) ?K" using hy hw G.sumset_mono subsetD 
                subset_refl by blast
            qed
            moreover have "G.sumset (G.sumset A B) ?K = G.sumset A B" 
              using G.sumset_commute G.sumset_stabilizer_eq_self G.sumset_subset_carrier by auto
            ultimately have "G.sumset {x'} (G.sumset A B) = G.sumset A B"
              by (metis G.finite_sumset G.sumset_subset_carrier card_subset_eq 
                G.card_sumset_singleton_subset_eq hA hB hx'G)
            then have "x' \<in> ?K" using hx'G by (meson empty_subsetI G.finite_sumset hA hB insert_subset 
              G.sumset_eq_sub_stabilizer G.sumset_subset_carrier)
            then show "x \<in> {K.Class [\<zero>]}" using hx\<phi> 
              by (metis K.Block_self K.Normal_def K.quotient.unit_closed insertCI)
          qed
        next
          show "{K.Class [\<zero>]} \<subseteq> GK.stabilizer (K.Class ` G.sumset A B)"
            using GK.zero_mem_stabilizer by auto
        qed
        interpret group_epimorphism ?\<phi> G "([\<oplus>])" "[\<zero>]" "G.Factor_Group G ?K" 
          K.quotient_composition "K.Class [\<zero>]" ..
        interpret GKN: normal_subgroup_in_kernel K.Class G "([\<oplus>])" "[\<zero>]" "G.Factor_Group G ?K" 
          K.quotient_composition "K.Class [\<zero>]" ?K 
        proof
          show "?K \<subseteq> Ker" using K.Block_self K.Normal_def K.quotient.unit_closed by blast
        qed
        have hsumK: "card (G.sumset A B) = card ?K * card (?\<phi> ` (G.sumset A B))"
          using G.finite_sumset hA hB G.sumset_subset_carrier G.Union_stabilizer_Class_eq 
          G.sumset_subset_carrier K.Union_Coset_card_eq by simp
        have hGKsumset: "GK.sumset (?\<phi> ` A) (?\<phi> ` B) = ?\<phi> ` (G.sumset A B)"
        proof
          show "GK.sumset (?\<phi> ` A) (?\<phi> ` B) \<subseteq> ?\<phi>  ` G.sumset A B"
          proof
            fix x assume "x \<in> GK.sumset (?\<phi> ` A) (?\<phi> ` B)"
            then obtain a b where ha: "a \<in> A" and hb: "b \<in> B" and 
              "x = K.quotient_composition (?\<phi> a) (?\<phi> b)" using GK.sumset.cases by blast
            then have "x = ?\<phi> (a [\<oplus>] b)" by (meson K.Class_commutes_with_composition hAG hBG in_mono)
            then show "x \<in> ?\<phi> ` G.sumset A B" using ha hb hAG hBG by blast
          qed
        next
          show "?\<phi>  ` G.sumset A B \<subseteq> GK.sumset (?\<phi> ` A) (?\<phi> ` B)"
          proof
            fix x assume "x \<in> ?\<phi> ` G.sumset A B"
            then obtain c where "c \<in> G.sumset A B" and "x = ?\<phi> c" by blast
            then obtain a b where "a \<in> A" and "b \<in> B" and "x = ?\<phi> (a [\<oplus>] b)" 
              using G.sumset.cases by metis
            then show "x \<in> GK.sumset (?\<phi> ` A) (?\<phi> ` B)" using GK.sumset.cases 
              K.Class_commutes_with_composition hAG hBG in_mono
              by (smt (verit, best) GK.sumset.simps K.natural.map_closed imageI)  
          qed
        qed
        have hAK: "card (G.sumset A ?K) = card ?K * card (?\<phi> ` A)" using hAG K.Union_Coset_card_eq hA
          G.sumset_stabilizer_eq_Class_Union G.Class_image_sumset_stabilizer_eq
          by (smt (verit, ccfv_threshold) card_0_eq G.card_sumset_0_iff G.finite_sumset hAne hB hBG hBne
            G.stabilizer_finite G.sumset_subset_carrier)
        have hBK: "card (G.sumset B ?K) = card ?K * card (?\<phi> ` B)" using hBG K.Union_Coset_card_eq hB 
          G.sumset_stabilizer_eq_Class_Union  G.Class_image_sumset_stabilizer_eq
          by (smt (verit, ccfv_SIG) card_0_eq G.card_sumset_0_iff G.finite_sumset hA hAG hAne hBne 
            G.stabilizer_finite G.sumset_subset_carrier)
        have "card (?\<phi> ` A) \<le> card A" by (simp add: card_image_le hA)
        moreover have "card (?\<phi> ` (G.sumset A B)) < card (G.sumset A B)" using hsumK hcardK_gt_1 
          G.card_sumset_0_iff hA hB hAne hBne by (metis card_eq_0_iff card_image_le hAG hBG 
          le_neq_implies_less less_not_refl3 mult_cancel2 nat_mult_1)
        ultimately have "card (GK.sumset (?\<phi> ` A) (?\<phi> ` B)) + card (?\<phi> ` A) < card (G.sumset A B) + card A" 
          using hGKsumset by auto
        then obtain m where "m < n" and "card (GK.sumset (?\<phi> ` A) (?\<phi> ` B)) + card (?\<phi> ` A) = m" 
          using hcardsum by blast
        moreover have h\<phi>Asub: "?\<phi> ` A \<subseteq> G.Factor_Group G ?K"
        proof
          fix x assume "x \<in> ?\<phi> ` A" then obtain a where "a \<in> G" and "?\<phi> a = x" using hAG by blast
          then show "x \<in> G.Factor_Group G ?K" by blast
        qed
        moreover have h\<phi>Bsub: "?\<phi> ` B \<subseteq> G.Factor_Group G ?K"
        proof
          fix x assume "x \<in> ?\<phi> ` B" then obtain b where "b \<in> G" and "?\<phi> b = x" using hBG by blast
          then show "x \<in> G.Factor_Group G ?K" by blast
        qed
        moreover have h\<phi>A: "finite (?\<phi> ` A)" and h\<phi>B: "finite (?\<phi> ` B)" and h\<phi>Ane: "?\<phi> ` A \<noteq> {}" and 
          h\<phi>Bne: "?\<phi> ` B \<noteq> {}" using hA hB hAne hBne by auto
        moreover have "additive_abelian_group (G.Factor_Group G ?K) K.quotient_composition 
          (K.Class [\<zero>])" ..
        moreover have "GK.stabilizer (GK.sumset (?\<phi> ` A) (?\<phi> ` B)) = {K.Class [\<zero>]}" 
          using hstab0 hGKsumset by auto
        ultimately have hind\<phi>: "card (GK.sumset (?\<phi> ` A) (?\<phi> ` B)) \<ge>  
          card (GK.sumset (?\<phi> ` A) {K.Class [\<zero>]}) + card (GK.sumset (?\<phi> ` B) {K.Class [\<zero>]}) - 1"
          using hindfactor[of "m" "?\<phi> ` A" "?\<phi> ` B"] by simp
        have h\<phi>sumA: "GK.sumset (?\<phi> ` A) {K.Class [\<zero>]} = ?\<phi> ` A"
          by (simp add: Int_absorb1 Int_commute h\<phi>Asub)
        have  h\<phi>sumB: "GK.sumset (?\<phi> ` B) {K.Class [\<zero>]} = ?\<phi> ` B"
          by (simp add: Int_absorb1 Int_commute h\<phi>Bsub)
        have "card (G.sumset A ?K) + card (G.sumset B ?K) - card ?K = 
          card ?K * (card (?\<phi> ` A) + card (?\<phi> ` B) - 1)" 
          using hAK hBK add_mult_distrib2 diff_mult_distrib2 nat_mult_1_right by presburger
        also have "... \<le> card ?K * card (GK.sumset (?\<phi> ` A) (?\<phi> ` B))" 
          using hind\<phi> h\<phi>sumA h\<phi>sumB by simp
        finally show ?thesis by (simp add: hGKsumset hsumK)
      qed   
    qed
  qed
  thus ?thesis using assms hAne hBne additive_abelian_group_axioms by blast
qed

subsection\<open>Strict version of Kneser's Theorem\<close>

text\<open>We show a strict version of Kneser's Theorem as presented in Theorem 3.2 of \cite{Ruzsa_book}.\<close>

theorem Kneser_strict_aux:  fixes A and B assumes hAG: "A \<subseteq> G" and hBG: "B \<subseteq> G" and hA: "finite A" 
  and hB: "finite B" and hAne: "A \<noteq> {}" and hBne: "B \<noteq> {}" and 
  hineq: "card (sumset A B) >  card (sumset A (stabilizer (sumset A B))) + 
  card (sumset B (stabilizer (sumset A B))) - card (stabilizer (sumset A B))" 
  shows "card (sumset A B) \<ge> card A + card B"

proof-
  let ?H = "stabilizer (sumset A B)"
  have hfin: "finite ?H" using stabilizer_subset_group stabilizer_finite sumset_subset_carrier 
      finite_sumset assms sumset_is_empty_iff sumset_stabilizer_eq_self by metis
  have "card ?H dvd card (sumset A B)" and "card ?H dvd (card (sumset A (stabilizer (sumset A B))) + 
  card (sumset B (stabilizer (sumset A B))) - card ?H)" 
    using card_stabilizer_divide_sumset hAG hBG card_stabilizer_sumset_divide_sumset by auto
  then have "card (sumset A B) \<ge> card (sumset A ?H) + card (sumset B ?H)" using hineq
    by (metis diff_le_mono2 dvd_add_right_iff dvd_imp_le le_diff_conv less_imp_add_positive)
  moreover have "card A + card B \<le> card (sumset A ?H) + card (sumset B ?H)" 
    using card_le_sumset sumset_commute assms stabilizer_subset_group stabilizer_is_nonempty 
      Int_emptyI inf.orderE add_mono hfin by metis
  ultimately show ?thesis by linarith
qed


theorem Kneser_strict:  fixes A and B assumes "A \<subseteq> G" and "B\<subseteq> G" and "finite A" and "finite B"
  and "stabilizer (sumset A B) = H" and "A \<noteq> {}" and "B \<noteq> {}" and " card (sumset A B) < card A + card B"
  shows "card (sumset A B) = card (sumset A (stabilizer (sumset A B))) + 
    card (sumset B (stabilizer (sumset A B))) - card (stabilizer (sumset A B))"
  using Kneser Kneser_strict_aux assms le_antisym nat_less_le by metis

subsection\<open>The Cauchy--Davenport Theorem\<close>

text\<open>We show the Cauchy--Davenport Theorem as a corollary of Kneser's Theorem, following a comment on
 Theorem 3.2 in \cite{Ruzsa_book}.\<close>


interpretation Z_p: additive_abelian_group "{0..int ((p :: nat)-1)}" "(\<lambda> x y. ((x + y) mod int p))" "0::int"
  using additive_abelian_group_def residue_group[of "p"] by fastforce

theorem Cauchy_Davenport:
  fixes p :: nat
  assumes "prime p" and "A \<noteq> {}" and "B \<noteq> {}" and "finite A" and "finite B" and 
    "A \<subseteq> {0..p-1}" and "B \<subseteq> {0..p-1}"
  shows "card (Z_p.sumset p A B) \<ge> Min {p, card A + card B -1}" 

proof(cases "Z_p.stabilizer p (Z_p.sumset p A B) = {0}")
  case True
  moreover have "Z_p.sumset p A {0} = A" and "Z_p.sumset p B {0} = B" using assms Z_p.sumset_D(1) by auto
  ultimately show ?thesis using Z_p.Kneser[of "A" "p" "B"] assms by fastforce
next
  case hne: False
  let ?H = "Z_p.stabilizer p (Z_p.sumset p A B)"
  have "?H = {0..int(p-1)}" using hne Z_p.stabilizer_is_subgroup[of "p" "Z_p.sumset p A B"] 
    residue_group_simple[OF assms(1)] by blast
  moreover have "p \<ge> 2" using assms(1) by (simp add: prime_ge_2_nat)
  ultimately have "card ?H = p" using card_atLeastAtMost by (simp add: of_nat_diff)
  then have "p \<le> card (Z_p.sumset p A B)" 
    using Z_p.card_stabilizer_le card_0_eq assms Z_p.card_sumset_0_iff Z_p.sumset.cases 
      Z_p.sumset_subset_carrier Z_p.finite_sumset by metis
  then show ?thesis by auto 
qed


end
end
