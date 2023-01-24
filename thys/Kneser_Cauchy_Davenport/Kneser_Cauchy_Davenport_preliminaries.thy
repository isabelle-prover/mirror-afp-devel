section\<open>Preliminaries\<close>

(*
  Session: Kneser_Cauchy_Davenport
  Title: Kneser_Cauchy_Davenport_preliminaries.thy
  Authors: Mantas Bakšys and Angeliki Koutsoukou-Argyraki 
  Affiliation: University of Cambridge
  Date: September 2022.
*)


theory Kneser_Cauchy_Davenport_preliminaries
  imports 
 Complex_Main
 "Pluennecke_Ruzsa_Inequality.Pluennecke_Ruzsa_Inequality"
  "HOL-Number_Theory.Prime_Powers"

begin

context subgroup_of_group

begin

interpretation left: left_translations_of_group ..
interpretation right: right_translations_of_group ..


interpretation transformation_group "left.translation ` H" G ..

lemma Right_Coset_eq_iff:
  assumes "x \<in> G" and "y \<in> G"
  shows "H |\<cdot> x = (H |\<cdot> y) \<longleftrightarrow> H |\<cdot> x \<inter> (H |\<cdot> y) \<noteq> {}"
  using assms Right_Coset_is_orbit 
  by (metis Int_absorb orbit.disjoint orbit.natural.map_closed orbit.non_vacuous)

end

context additive_abelian_group


begin


subsection\<open>Elementary lemmas on sumsets \<close> (*this subsection can be moved to
 Pluennecke_Ruzsa_Inequality. *)

lemma sumset_translate_eq_right:
  assumes "A \<subseteq> G" and "B \<subseteq> G" and "x \<in> G"
  shows "(sumset A {x} = sumset B {x}) \<longleftrightarrow>  A = B" using assms  
  by (smt (verit, best) Diff_Int_distrib2 Diff_eq_empty_iff
 Int_Un_eq(1) Int_absorb2 Un_Diff_cancel2 Un_commute insert_disjoint(2) 
subset_refl sumset_is_empty_iff sumsetdiff_sing)

lemma sumset_translate_eq_left:
  assumes "A \<subseteq> G" and "B \<subseteq> G" and "x \<in> G"
  shows " (sumset {x} A = sumset {x} B) \<longleftrightarrow> A = B" using assms
  by (simp add: sumset_commute sumset_translate_eq_right) 

lemma differenceset_translate_eq_right:
  assumes "A \<subseteq> G" and "B \<subseteq> G" and "x \<in> G"
  shows "(differenceset A {x} = differenceset B {x}) \<longleftrightarrow> A = B" using assms
  by (metis Int_absorb2 differenceset_commute minus_minusset minusset_subset_carrier 
    sumset_translate_eq_left)

lemma differenceset_translate_eq_left:
  assumes "A \<subseteq> G" and "B \<subseteq> G" and "x \<in> G"
  shows "(differenceset {x} A = differenceset {x} B) \<longleftrightarrow> A = B" using assms
  by (metis differenceset_commute differenceset_translate_eq_right)

lemma sumset_inter_union_subset:
 "sumset (A \<inter> B) (A \<union> B) \<subseteq> sumset A B"
  by (metis Int_Diff_Un Int_Un_eq(2) Un_subset_iff sumset_commute sumset_subset_Un(2) 
    sumset_subset_Un2)

lemma differenceset_group_eq:
  "G = differenceset G G" 
  using equalityE minusset_eq minusset_triv subset_antisym sumset_D(1) sumset_subset_carrier 
    sumset_mono image_mono Int_absorb by metis

lemma card_sumset_singleton_subset_eq:
  assumes "a \<in> G" and "A \<subseteq> G"
  shows "card (sumset {a} A) = card A"
  using assms card_sumset_singleton_eq card.infinite card_sumset_0_iff' le_iff_inf sumset_commute 
  by metis

lemma card_differenceset_singleton_mem_eq:
  assumes "a \<in> G" and "A \<subseteq> G"
  shows "card A = card (differenceset A {a})"
  using assms by (metis card_minusset' card_sumset_singleton_subset_eq differenceset_commute 
  minusset_subset_carrier)

lemma card_singleton_differenceset_eq:
  assumes "a \<in> G" and "A \<subseteq> G"
  shows "card A = card (differenceset {a} A)"
  using assms by (metis card_minusset' card_sumset_singleton_subset_eq minusset_subset_carrier)

lemma sumset_eq_Union_left:
  assumes "A \<subseteq> G"
  shows "sumset A B = (\<Union> a \<in> A. sumset {a} B)"
proof
  show "sumset A B \<subseteq> (\<Union> a \<in> A. sumset {a} B)"
    using assms sumset.cases Int_absorb2 Int_iff UN_iff singletonI sumset.sumsetI
    by (smt (verit, del_insts) subsetI)
  next
    show "(\<Union> a \<in> A. sumset {a} B) \<subseteq> sumset A B"
      using sumset by auto
  qed

lemma sumset_eq_Union_right:
  assumes "B \<subseteq> G"
  shows "sumset A B = (\<Union> b \<in> B. sumset A {b})" 
  using assms sumset_commute sumset_eq_Union_left by (metis (no_types, lifting) Sup.SUP_cong)


lemma sumset_singletons_eq: 
  assumes "a \<in> G" and "b \<in> G"
  shows "sumset {a} {b} = {a \<oplus> b}"
  using assms sumset.simps subset_antisym by auto

lemma sumset_eq_subset_differenceset:
  assumes "K \<subseteq> G" and "K \<noteq> {}" and "A \<subseteq> G" and "sumset A K = sumset B K"
  shows "A \<subseteq> differenceset (sumset B K) K"
proof
  fix a assume ha: "a \<in> A"
  obtain k where hk: "k \<in> K" using assms(2) by blast
  then have "a \<oplus> k \<in> sumset B K" using assms sumset.sumsetI ha by blast
  then have "a \<oplus> (k \<ominus> k) \<in> differenceset (sumset B K) K" using hk assms ha minusset.minussetI 
    subset_iff sumset.sumsetI by (smt (verit) associative composition_closed inverse_closed)
  then show "a \<in> differenceset (sumset B K) K" using hk ha subsetD assms right_unit
    by (metis invertible invertible_right_inverse)
qed 

end

locale subgroup_of_additive_abelian_group = 
  subgroup_of_abelian_group H G "(\<oplus>)" \<zero> + additive_abelian_group G "(\<oplus>)" \<zero> 
  for H G and addition (infixl "\<oplus>" 65)  and zero ("\<zero>")

begin 

notation Left_Coset  (infixl "\<cdot>|" 70)

lemma Left_Coset_eq_sumset:
  assumes "x \<in> G"
  shows "sumset {x} H = x \<cdot>| H" 
  using assms Left_Coset_memI sumset.simps by fastforce

lemma sumset_subgroup_eq_iff:
  assumes "a \<in> G" and "b \<in> G"
  shows "sumset {a} H = sumset {b} H \<longleftrightarrow> 
    (sumset {a} H) \<inter> (sumset {b} H) \<noteq> {}" 
  using Right_Coset_eq_iff assms Left_Coset_eq_sumset Left_equals_Right_coset by presburger

lemma card_divide_sumset:
  assumes "A \<subseteq> G"
  shows "card H dvd card (sumset A H)"
proof(cases "finite H \<and> finite A")
  case hfin: True
  then have hfinsum: "\<And> X. X \<in> ((\<lambda> a. sumset {a} H) ` A) \<Longrightarrow> finite X"
    using finite_sumset by force
  moreover have "pairwise disjnt ((\<lambda> a. sumset {a} H) ` A)"
    using pairwise_imageI disjnt_def sumset_subgroup_eq_iff subset_eq assms by (smt (verit, best))
  moreover have "card H dvd sum card ((\<lambda> a. sumset {a} H) ` A)"
  proof(intro dvd_sum)
    fix X assume "X \<in> (\<lambda> a. sumset {a} H) ` A"
    then show "card H dvd card X" using dvd_refl
      using Left_equals_Right_coset Right_Coset_cardinality assms Left_Coset_eq_sumset by auto
  qed
  ultimately show ?thesis using assms sumset_eq_Union_left card_Union_disjoint by metis
next
  case False
  then show ?thesis using assms card_sumset_0_iff by (metis card_eq_0_iff dvd_0_right sub subsetI)
qed

lemma sumset_subgroup_eq_Class_Union:
  assumes "A \<subseteq> G"
  shows "sumset A H = (\<Union> (Class ` A))"
proof
  show "sumset A H \<subseteq> \<Union> (Class ` A)"
  proof
    fix x assume "x \<in> sumset A H"
    then obtain a b where ha: "a \<in> A" and "b \<in> H" and "x = a \<oplus> b" 
      using sumset.cases by blast
    then have "x \<in> Class a" using Left_Coset_Class_unit Left_Coset_eq_sumset assms by blast
    thus "x \<in> \<Union> (Class ` A)" using ha by blast 
  qed
next
  show "\<Union> (Class ` A) \<subseteq> sumset A H"
  proof(intro Union_least)
    fix X assume "X \<in> Class ` A"
    then obtain a where "a \<in> A" and "X = Class a" by blast
    moreover hence "{a} \<subseteq> A" by auto 
    ultimately show "X \<subseteq> sumset A H" using Left_Coset_Class_unit 
      Left_Coset_eq_sumset assms sumset_mono subset_refl in_mono by metis
  qed
qed

lemma Class_image_sumset_subgroup_eq:
  assumes "A \<subseteq> G"
  shows "Class ` (sumset A H) = Class ` A"
proof
  show "Class ` sumset A H \<subseteq> Class ` A"
  proof
    fix x assume "x \<in> Class ` sumset A H"
    then obtain c where hc: "c \<in> sumset A H" and "x = Class c" by blast
    moreover obtain a b where ha: "a \<in> A" and "b \<in> H" and "c = a \<oplus> b" using hc sumset.cases
      by blast
    ultimately show "x \<in> Class ` A" using ha Class_eq CongruenceI assms composition_closed 
      sumset.cases Partition_def commutative image_eqI left_unit sub unit_closed 
      by (smt (verit, ccfv_threshold) Block_self Class_cong Normal_def)
  qed
next
  show "Class ` A \<subseteq> Class ` sumset A H" using assms right_unit subsetD subsetI sumset.sumsetI 
    unit_closed by (smt (verit, del_insts) image_subset_iff sub_unit_closed) 
qed

lemma Class_cover_imp_subset_or_disj:
  assumes "A = (\<Union> (Class ` C))" and "x \<in> G" and "C \<subseteq> G"
  shows "Class x \<subseteq> A \<or> Class x \<inter> A = {}"
proof(intro disjCI)
  assume "Class x \<inter> A \<noteq> {}"
  then obtain c where "c \<in> C" and "Class x \<inter> Class c \<noteq> {}" using assms by blast
  then show "Class x \<subseteq> A" using assms not_disjoint_implies_equal Sup_upper imageI subset_iff 
    by blast
qed
  
end

context additive_abelian_group

begin

subsection\<open>Stabilizer and basic properties\<close>


text\<open>We define the stabilizer or group of periods of a nonempty subset of an abelian group.\<close>

definition stabilizer::"'a set \<Rightarrow> 'a set " where
"stabilizer S \<equiv> {x \<in> G. sumset {x} (S \<inter> G) = S \<inter> G}"

lemma stabilizer_is_subgroup: fixes S :: "'a set"
  shows "subgroup (stabilizer S) G (\<oplus>) (\<zero>)"
proof (intro subgroupI)
  show "stabilizer S \<subseteq> G" using stabilizer_def by auto
next
  show "\<zero> \<in> stabilizer S" using stabilizer_def by (simp add: Int_absorb1 Int_commute)
next
  fix a b assume haS: "a \<in> stabilizer S" and hbS: "b \<in> stabilizer S"
  then have haG: "a \<in> G" and hbG: "b \<in> G" using stabilizer_def by auto
  have "sumset {a \<oplus> b} (S \<inter> G) = sumset {a} (sumset {b} (S \<inter> G))"
  proof
    show "sumset {a \<oplus> b} (S \<inter> G) \<subseteq> sumset {a} (sumset {b} (S \<inter> G))" using haG hbG
      empty_subsetI insert_subset subsetI sumset.simps sumset_assoc sumset_mono
      by metis
    show "sumset {a} (sumset {b} (S \<inter> G)) \<subseteq> sumset {a \<oplus> b} (S \<inter> G)" 
      using empty_iff insert_iff sumset.simps sumset_assoc by (smt (verit, best) subsetI)
  qed
  then show "a \<oplus> b \<in> stabilizer S" using haS hbS stabilizer_def by auto
next
  fix g assume "g \<in> stabilizer S"
  thus "invertible g" using stabilizer_def by auto
next
  fix g assume hgS: "g \<in> stabilizer S"
  then have hinvsum : "inverse g \<oplus> g = \<zero>" using stabilizer_def by simp
  have "sumset {inverse g} (sumset {g}  (S \<inter> G)) =  (S \<inter> G)"
  proof
    show "sumset {inverse g} (sumset {g} (S \<inter> G)) \<subseteq> (S \<inter> G)" using 
      empty_iff insert_iff sumset.simps sumset_assoc subsetI left_unit hinvsum
      by (smt (verit, ccfv_threshold))
    show "(S \<inter> G) \<subseteq> sumset {inverse g} (sumset {g} (S \<inter> G))"
    proof
      fix s assume hs: "s \<in> (S \<inter> G)"
      then have "inverse g \<oplus> g \<oplus> s \<in> sumset {inverse g} (sumset {g} (S \<inter> G))" using
        hgS stabilizer_def additive_abelian_group.sumset.sumsetI 
        additive_abelian_group_axioms associative in_mono inverse_closed mem_Collect_eq singletonI
        by (smt (z3) IntD2)
      thus "s \<in> sumset {inverse g} (sumset {g} (S \<inter> G))" using hinvsum hs 
        by simp
    qed
  qed
  thus "inverse g \<in> stabilizer S" using hgS stabilizer_def by auto
qed

interpretation subgroup_of_additive_abelian_group "stabilizer A" "G" "(\<oplus>)" "\<zero>"
  using stabilizer_is_subgroup subgroup_of_abelian_group_def
  by (metis abelian_group_axioms additive_abelian_group_axioms group_axioms 
    subgroup_of_additive_abelian_group_def subgroup_of_group_def)

lemma zero_mem_stabilizer: "\<zero> \<in> stabilizer A" ..

lemma stabilizer_is_nonempty:
  shows "stabilizer S \<noteq> {}" 
  using sub_unit_closed by blast

lemma Left_Coset_eq_sumset_stabilizer:
  assumes "x \<in> G"
  shows "sumset {x} (stabilizer B) = x \<cdot>| (stabilizer B)" 
  by (simp add: Left_Coset_eq_sumset assms)

lemma stabilizer_subset_difference_singleton:
  assumes "S \<subseteq> G" and "s \<in> S"
  shows "stabilizer S \<subseteq> differenceset S {s}"
proof
  fix x assume hx: "x \<in> stabilizer S"
  then obtain t where ht: "t \<in> S" and "x \<oplus> s = t" using assms stabilizer_def by blast
  then have "x = t \<ominus> s" using hx stabilizer_def assms associative
    by (metis (no_types, lifting) in_mono inverse_closed invertible invertible_right_inverse sub 
      sub.right_unit)
  thus "x \<in> differenceset S {s}" using ht assms
    by (simp add: minusset.minussetI subsetD sumset.sumsetI)
qed

lemma stabilizer_subset_singleton_difference:
  assumes "S \<subseteq> G" and "s \<in> S"
  shows "stabilizer S \<subseteq> differenceset {s} S"
proof-
  have "stabilizer S \<subseteq> minusset (stabilizer S)" using assms Int_absorb2 minusset_eq 
    subgroup.image_of_inverse submonoid.sub subset_eq
    by (smt (verit) stabilizer_is_subgroup stabilizer_subset_difference_singleton 
      sumset_subset_carrier)
  moreover have "minusset (stabilizer S) \<subseteq> minusset (differenceset S {s})" 
  proof
    fix x assume hx1: "x \<in> minusset (stabilizer S)"
    then have hx: "inverse x \<in> stabilizer S"
      by (metis invertible invertible_inverse_inverse minusset.cases)
    then obtain t where ht: "t \<in> S" and "inverse x \<oplus> s = t" using assms stabilizer_def by blast
    then have hx2: "inverse x = t \<ominus> s" using hx stabilizer_def assms
      by (smt (verit, ccfv_threshold) commutative in_mono inverse_closed invertible 
        invertible_left_inverse2 sub)
    thus "x \<in> minusset (differenceset S {s})" using ht assms 
      by (smt (verit, best) hx1 additive_abelian_group.sumset.sumsetI additive_abelian_group_axioms 
        inverse_closed invertible invertible_inverse_inverse minusset.cases minusset.minussetI 
        singletonI subset_iff)
  qed
  ultimately show ?thesis using differenceset_commute assms by blast
qed

lemma stabilizer_subset_nempty: 
  assumes "S \<noteq> {}" and "S \<subseteq> G"
  shows "stabilizer S \<subseteq> differenceset S S"
proof
  fix x assume hx: "x \<in> stabilizer S"
  then obtain s where hs: "s \<in> S \<inter> G" using assms by blast
  then have "x \<oplus> s \<in> S \<inter> G" using stabilizer_def assms hx mem_Collect_eq singletonI 
    sumset.sumsetI sumset_Int_carrier by blast
  then obtain t where ht: "t \<in> S" and "x \<oplus> s = t" by blast
  then have "x = t \<ominus> s" using hx stabilizer_def assms(2) hs ht associative
    by (metis IntD2 inverse_closed invertible invertible_right_inverse sub sub.right_unit)
  thus "x \<in> differenceset S S" using ht hs using assms(2) by blast 
qed

lemma stabilizer_coset_subset:
  assumes "A \<subseteq> G" and "x \<in> A"
  shows "sumset {x} (stabilizer A) \<subseteq> A"
proof
  fix y assume "y \<in> sumset {x} (stabilizer A)"
  moreover hence "stabilizer A \<subseteq> differenceset A {x}" using assms 
      stabilizer_subset_difference_singleton by auto
  moreover have "sumset {x} (differenceset A {x}) \<subseteq> A"
  proof
    fix z assume "z \<in> sumset {x} (differenceset A {x})"
    then obtain a where "a \<in> A" and "z = x \<oplus> (a \<ominus> x)" 
      using additive_abelian_group.sumset.cases additive_abelian_group_axioms singletonD 
        minusset.cases assms subsetD by (smt (verit, ccfv_SIG))
    thus "z \<in> A" using assms
        by (metis additive_abelian_group.inverse_closed additive_abelian_group_axioms
          commutative in_mono invertible invertible_right_inverse2)
    qed
    ultimately show "y \<in> A" by (meson in_mono subset_singleton_iff sumset_mono) 
  qed

lemma stabilizer_subset_stabilizer_dvd:
  assumes "stabilizer A \<subseteq> stabilizer B"
  shows "card (stabilizer A) dvd card (stabilizer B)"
proof(cases "finite (stabilizer B)")
  case hB: True
  interpret H: subgroup_of_group "stabilizer A" "stabilizer B" "(\<oplus>)" "\<zero>"
  proof(unfold_locales)
    show "stabilizer A \<subseteq> stabilizer B" using assms by blast
  next
    show "\<And>a b. a \<in> stabilizer A \<Longrightarrow> b \<in> stabilizer A \<Longrightarrow> a \<oplus> b \<in> stabilizer A" 
      using stabilizer_is_subgroup group_axioms by simp
  next
    show "\<zero> \<in> stabilizer A" using sub_unit_closed by blast
  qed
  show ?thesis using H.lagrange hB by auto
next
  case False
  then show ?thesis by simp
qed

lemma stabilizer_coset_Un:
  assumes "A \<subseteq> G"
  shows "(\<Union> x \<in> A. sumset {x} (stabilizer A)) = A"
proof
  show "(\<Union>x\<in>A. sumset {x} (stabilizer A)) \<subseteq> A"
    using stabilizer_coset_subset assms by blast
next
  show "A \<subseteq> (\<Union>x\<in>A. sumset {x} (stabilizer A))"
  proof
    fix x assume hx: "x \<in> A"
    then have "x \<in> sumset {x} (stabilizer A)" using sub_unit_closed assms
      by (metis in_mono right_unit singletonI sumset.sumsetI unit_closed) 
    thus "x \<in> (\<Union>x\<in>A. sumset {x} (stabilizer A))" using hx by blast
  qed
qed
  
lemma stabilizer_empty: "stabilizer {} = G" 
  using sumset_empty Int_empty_left stabilizer_def subset_antisym
  by (smt (verit, best) mem_Collect_eq subsetI sumset_Int_carrier_eq(1) sumset_commute)
  
lemma stabilizer_finite:
  assumes "S \<subseteq> G" and "S \<noteq> {}" and "finite S"
  shows "finite (stabilizer S)"
  using stabilizer_subset_nempty assms
  by (meson finite_minusset finite_sumset rev_finite_subset)

lemma stabilizer_subset_group:
  shows "stabilizer S \<subseteq> G" using stabilizer_def by blast

lemma sumset_stabilizer_eq_iff:
  assumes "a \<in> G" and "b \<in> G"
  shows "sumset {a} (stabilizer A) = sumset {b} (stabilizer A) \<longleftrightarrow> 
    (sumset {a} (stabilizer A)) \<inter> (sumset {b} (stabilizer A)) \<noteq> {}"
  by (simp add: assms sumset_subgroup_eq_iff)

lemma sumset_stabilizer_eq_Class_Union:
  assumes "A \<subseteq> G"
  shows "sumset A (stabilizer B) = (\<Union> (Class B ` A))"
  by (simp add: assms sumset_subgroup_eq_Class_Union)

lemma card_stabilizer_divide_sumset:
  assumes "A \<subseteq> G"
  shows "card (stabilizer B) dvd card (sumset A (stabilizer B))" 
  by (simp add: assms card_divide_sumset)

lemma Class_image_sumset_stabilizer_eq:
  assumes "A \<subseteq> G"
  shows "Class B ` (sumset A (stabilizer B)) = Class B ` A"
  by (simp add: Class_image_sumset_subgroup_eq assms)

lemma Class_cover_imp_subset_or_disj:
  assumes "A = (\<Union> (Class B ` C))" and "x \<in> G" and "C \<subseteq> G"
  shows "Class B x \<subseteq> A \<or> Class B x \<inter> A = {}"
  by (simp add: Class_cover_imp_subset_or_disj assms)

lemma stabilizer_sumset_disjoint:
  fixes S1 S2 :: "'a set"
  assumes "stabilizer S1 \<inter> stabilizer S2 = {\<zero>}" and "S1 \<subseteq> G" and "S2 \<subseteq> G"
    and "finite S1" and "finite S2" and "S1 \<noteq> {}" and "S2 \<noteq> {}"
  shows "card (sumset (stabilizer S1) (stabilizer S2)) = 
    card (stabilizer S1) * card (stabilizer S2)"
proof-
  have inj_on : "inj_on (\<lambda> (a, b). a \<oplus> b) (stabilizer S1 \<times> stabilizer S2)"
  proof(intro inj_onI) 
    fix x y assume "x \<in> stabilizer S1 \<times> stabilizer S2" and "y \<in> stabilizer S1 \<times> stabilizer S2" and
      "(case x of (a, b) \<Rightarrow> a \<oplus> b) = (case y of (a, b) \<Rightarrow> a \<oplus> b)"
    then obtain a b c d where hx: "x = (a, b)" and hy: "y = (c, d)" and ha: "a \<in> stabilizer S1" and
      hb: "b \<in> stabilizer S2" and hc: "c \<in> stabilizer S1" and hd: "d \<in> stabilizer S2" and 
      habcd: "a \<oplus> b = c \<oplus> d" by auto
    then have haG: "a \<in> G" using stabilizer_def by blast
    have hbG: "b \<in> G" using hb stabilizer_def by blast 
    have hcG: "c \<in> G" using hc stabilizer_def by blast
    have hdG: "d \<in> G" using hd stabilizer_def by blast 
    then have "a \<ominus> c = d \<ominus> b" using habcd haG hbG hcG hdG
      by (metis (full_types) associative commutative composition_closed inverse_equality invertible 
        invertible_def invertible_left_inverse2)
    moreover have "a \<ominus> c \<in> stabilizer S1" using ha hc stabilizer_is_subgroup
      subgroup.axioms(1) submonoid.sub_composition_closed
      by (metis group.invertible group_axioms hcG subgroup.subgroup_inverse_iff)
    moreover have "d \<ominus> b \<in> stabilizer S2" using hd hb  stabilizer_is_subgroup
      subgroup.axioms(1) submonoid.sub_composition_closed
      by (metis group.invertible group_axioms hbG subgroup.subgroup_inverse_iff)
    ultimately have "a \<ominus> c = \<zero>" and "d \<ominus> b = \<zero>" using assms(1) by auto
    thus "x = y" using hx hy haG hbG hcG hdG
      by (metis inverse_closed invertible invertible_right_cancel invertible_right_inverse)    
  qed
  moreover have himage : "(\<lambda> (a, b). a \<oplus> b) ` (stabilizer S1 \<times> stabilizer S2) = 
    sumset (stabilizer S1) (stabilizer S2)"
  proof
    show "(\<lambda>(a, b). a \<oplus> b) ` (stabilizer S1 \<times> stabilizer S2) \<subseteq> sumset (stabilizer S1) (stabilizer S2)"
      using stabilizer_subset_group by force

  next
    show "sumset (stabilizer S1) (stabilizer S2) \<subseteq> (\<lambda>(a, b). a \<oplus> b) ` (stabilizer S1 \<times> stabilizer S2)"
    proof
      fix x assume "x \<in> sumset (stabilizer S1) (stabilizer S2)"
      then obtain s1 s2 where hs1: "s1 \<in> stabilizer S1" and hs2: "s2 \<in> stabilizer S2" and 
        "x = s1 \<oplus> s2" by (meson sumset.cases)
      thus "x \<in> (\<lambda>(a, b). a \<oplus> b) ` (stabilizer S1 \<times> stabilizer S2)" using hs1 hs2 by auto
    qed
  qed
  ultimately show ?thesis using card_image card_cartesian_product by fastforce
qed

lemma stabilizer_sub_sumset_left:
  "stabilizer A \<subseteq> stabilizer (sumset A B)"
proof
  fix x assume hx: "x \<in> stabilizer A"
  then have "sumset {x} (sumset A B) = sumset A B" using stabilizer_def sumset_assoc 
    mem_Collect_eq by (smt (verit, del_insts) sumset_Int_carrier_eq(1) sumset_commute)
  thus "x \<in> stabilizer (sumset A B)" using hx stabilizer_def
    by (metis (mono_tags, lifting) mem_Collect_eq sumset_Int_carrier)
qed

lemma stabilizer_sub_sumset_right:
  "stabilizer B \<subseteq> stabilizer (sumset A B)"
  using stabilizer_sub_sumset_left sumset_commute by fastforce

lemma not_mem_stabilizer_obtain:
  assumes "A \<noteq> {}" and "x \<notin> stabilizer A" and "x \<in> G" and "A \<subseteq> G" and "finite A"
  obtains a where "a \<in> A" and "x \<oplus> a \<notin> A"
proof-
  have "sumset {x} A \<noteq> A" using assms stabilizer_def
    by (metis (mono_tags, lifting) inf.orderE mem_Collect_eq)
  moreover have "card (sumset {x} A) = card A" using assms
    by (metis card_sumset_singleton_eq inf.orderE sumset_commute)
  ultimately obtain y where "y \<in> sumset {x} A" and "y \<notin> A" using assms 
    by (meson card_subset_eq subsetI)
  then obtain a where "a \<in> A" and "x \<oplus> a \<notin> A" using assms
    by (metis singletonD sumset.cases)
  thus ?thesis using that by blast 
qed

lemma sumset_eq_sub_stabilizer:
  assumes "A \<subseteq> G" and "B \<subseteq> G" and "finite B"
  shows "sumset A B = B \<Longrightarrow> A \<subseteq> stabilizer B" 
proof
  fix x assume hsum: "sumset A B = B" and hx: "x \<in> A"
  have "sumset {x} B = B"
  proof-
    have "sumset {x} B \<subseteq> B" using hsum hx
      by (metis empty_subsetI equalityE insert_subset sumset_mono)
    moreover have "card (sumset {x} B) = card B" using assms
      by (metis IntD1 Int_absorb1 card_sumset_singleton_eq hx inf_commute sumset_commute)
    ultimately show ?thesis using card_subset_eq assms(3) by auto
  qed
  thus "x \<in> stabilizer B" using hx assms(1) stabilizer_def
    by (metis (mono_tags, lifting) assms(2) inf.orderE mem_Collect_eq subsetD)
qed


lemma sumset_stabilizer_eq:
  shows "sumset (stabilizer A) (stabilizer A) = stabilizer A"
proof
  show "sumset (stabilizer A) (stabilizer A) \<subseteq> stabilizer A"
    using stabilizer_is_subgroup subgroup.axioms(1) subsetI
    by (metis (mono_tags, lifting) additive_abelian_group.sumset.simps additive_abelian_group_axioms 
      submonoid.sub_composition_closed)
next
  show "stabilizer A \<subseteq> sumset (stabilizer A) (stabilizer A)"
    using Left_Coset_eq_sumset stabilizer_is_nonempty 
      stabilizer_subset_group sub_unit_closed additive_abelian_group_axioms right_unit 
      subset_iff sumsetI by (smt (verit, best))
qed
  

lemma differenceset_stabilizer_eq:
  shows "differenceset (stabilizer A) (stabilizer A) = stabilizer A"
proof
  show "differenceset (stabilizer A) (stabilizer A) \<subseteq> stabilizer A"
  proof
    fix x assume "x \<in> differenceset (stabilizer A) (stabilizer A)"
    then obtain a b where "a \<in> stabilizer A" and "b \<in> stabilizer A" and "x = a \<ominus> b"
      by (metis minusset.cases sumset.cases)
    thus "x \<in> stabilizer A" using stabilizer_is_subgroup subgroup.axioms(1)
      by (smt (verit, ccfv_threshold) in_mono invertible stabilizer_subset_group 
        subgroup_inverse_iff sub_composition_closed) 
  qed
next
  show "stabilizer A \<subseteq> differenceset (stabilizer A) (stabilizer A)"
  proof
    fix x assume hx: "x \<in> stabilizer A"
    then have "x \<ominus> \<zero> \<in> differenceset (stabilizer A) (stabilizer A)" by blast
    then show "x \<in> differenceset (stabilizer A) (stabilizer A)" using hx by simp
  qed
qed

lemma stabilizer2_sub_stabilizer:
  shows "stabilizer(stabilizer A) \<subseteq> stabilizer A"
proof(cases "A \<noteq> {}")
  case True
  then have "stabilizer(stabilizer A) \<subseteq> differenceset (stabilizer A) (stabilizer A)"
    by (simp add: stabilizer_is_nonempty stabilizer_subset_group stabilizer_subset_nempty)
  thus ?thesis using differenceset_stabilizer_eq by blast
next
  case False
  then show ?thesis by (simp add: stabilizer_empty stabilizer_subset_group)
qed

lemma stabilizer_left_sumset_invariant:
  assumes "a \<in> G" and "A \<subseteq> G"
  shows "stabilizer (sumset {a} A) = stabilizer A"

proof
  show "stabilizer (sumset {a} A) \<subseteq> stabilizer A"
  proof
    fix x assume hx: "x \<in> stabilizer (sumset {a} A)"
    then have hxG: "x \<in> G" using stabilizer_def by blast 
    have "sumset {x} (sumset {a} A) = sumset {a} A" using stabilizer_def hx
      by (metis (mono_tags, lifting) mem_Collect_eq sumset_Int_carrier)
    then have "sumset {x} A = A" using assms
      by (metis (full_types) sumset_assoc sumset_commute sumset_subset_carrier 
          sumset_translate_eq_right)
    thus "x \<in> stabilizer A" using hxG stabilizer_def
      by (metis (mono_tags, lifting) mem_Collect_eq sumset_Int_carrier)
  qed
next
  show "stabilizer A \<subseteq> stabilizer (sumset {a} A)" using stabilizer_def
    using stabilizer_sub_sumset_right by meson
qed

lemma stabilizer_right_sumset_invariant:
  assumes "a \<in> G" and "A \<subseteq> G"
  shows "stabilizer (sumset A {a}) = stabilizer A" 
  using sumset_commute stabilizer_left_sumset_invariant assms by simp

lemma stabilizer_right_differenceset_invariant:
  assumes "b \<in> G" and "A \<subseteq> G"
  shows "stabilizer (differenceset A {b}) = stabilizer A"
  using assms minusset_eq stabilizer_right_sumset_invariant by auto

lemma stabilizer_unchanged:
  assumes "a \<in> G" and "b \<in> G"
  shows "stabilizer (sumset A B) = stabilizer (sumset A (sumset (differenceset B {b}) {a}))"

proof-
  have "sumset A (sumset (differenceset B {b}) {a}) = sumset (differenceset (sumset A B) {b}) {a}"
    by (simp add: sumset_assoc)
  thus ?thesis using stabilizer_right_sumset_invariant 
    stabilizer_right_differenceset_invariant assms sumset_subset_carrier by simp
qed


lemma subset_stabilizer_of_subset_sumset:
  assumes "A \<subseteq> sumset {x} (stabilizer B)" and "x \<in> G" and "A \<noteq> {}" and "A \<subseteq> G"
  shows "stabilizer A \<subseteq> stabilizer B"
proof-
  obtain a where ha: "a \<in> A" using assms by blast
  moreover then obtain b where hb: "b \<in> stabilizer B" and haxb: "a = x \<oplus> b" using sumset.cases assms by blast
  ultimately have "stabilizer A \<subseteq> differenceset A {a}" using assms sumset_subset_carrier 
    stabilizer_subset_difference_singleton by (meson subset_trans)
  also have "... = sumset {inverse a} A" using sumset_commute ha assms(4) inverse_closed 
    subsetD minusset_eq by auto
  also have "... \<subseteq> sumset {inverse x \<oplus> inverse b} (sumset {x} (stabilizer B))" 
    using assms sumset_mono haxb inverse_closed hb stabilizer_subset_group subsetD 
    commutative inverse_composition_commute by (metis invertible subset_singleton_iff)
  also have "... = sumset {inverse b} (stabilizer B)" using sumset_singletons_eq commutative
      assms sumset_assoc hb stabilizer_subset_group inverse_closed invertible
    by (metis composition_closed invertible_right_inverse2 sub)
  also have "... = stabilizer B" using hb Left_Coset_eq_sumset sub_unit_closed sub subset_iff
    additive_abelian_group_axioms calculation disjoint_iff_not_equal factor_unit inverse_closed 
    sumset_subgroup_eq_iff by (smt (verit, del_insts))
  finally show ?thesis . 
qed

lemma sumset_stabilizer_eq_self:
  assumes "A \<subseteq> G"
  shows "sumset (stabilizer A) A = A" 
  using assms sumset_eq_Union_left[OF "stabilizer_subset_group"] 
    Int_absorb2 stabilizer_coset_Un sumset_commute sumset_eq_Union_left by presburger

lemma stabilizer_neq_subset_sumset:
  assumes "A \<subseteq> sumset {x} (stabilizer B)" and "x \<in> A" and "\<not> sumset {x} (stabilizer B) \<subseteq> C" and 
    "A \<subseteq> C" and "C \<subseteq> G"
  shows "stabilizer A \<noteq> stabilizer B"
proof
  assume heq: "stabilizer A = stabilizer B"
  obtain a where "a \<in> sumset {x} (stabilizer B)" and 
    "a \<notin> C" using assms by blast
  moreover then obtain b where "b \<in> stabilizer B" and "a = x \<oplus> b" using sumset.cases by blast
  ultimately have "b \<oplus> x \<notin> A" using commutative stabilizer_subset_group assms in_mono by metis
  thus False using assms heq stabilizer_coset_subset subset_trans by metis
qed

lemma subset_stabilizer_Un:
  shows "stabilizer A \<inter> stabilizer B \<subseteq> stabilizer (A \<union> B)"
proof
  fix x assume hx: "x \<in> stabilizer A \<inter> stabilizer B"
  then have "sumset {x} (A \<inter> G) = A \<inter> G" using stabilizer_def by blast
  moreover have "sumset {x} (B \<inter> G) = (B \<inter> G)" using stabilizer_def hx by blast
  ultimately have "sumset {x} ((A \<union> B) \<inter> G) = (A \<union> B) \<inter> G" using sumset_subset_Un2 
    boolean_algebra.conj_disj_distrib2 by auto
  then show "x \<in> stabilizer (A \<union> B)" using hx stabilizer_subset_group stabilizer_def by blast
qed

lemma mem_stabilizer_Un_and_left_imp_right:
  assumes "finite B" and "x \<in> stabilizer (A \<union> B)" and "x \<in> stabilizer A" and "disjnt A B"
  shows "x \<in> stabilizer B"
proof-
  have "(A \<inter> G) \<union> sumset {x} (B \<inter> G) = (A \<inter> G) \<union> (B \<inter> G)" 
    using assms(2) sumset_subset_Un2[of "{x}" "A \<inter> G" "B \<inter> G"] stabilizer_def[of "A \<union> B"] 
    Int_Un_distrib2[of "A" "B" "G"] assms(3) stabilizer_def 
    by (metis (mono_tags, lifting) mem_Collect_eq)
  then have "B \<inter> G \<subseteq> sumset {x} (B \<inter> G)" using assms(4) disjnt_def Int_Un_distrib2 Int_commute 
    sumset_subset_Un1 by (smt (verit, del_insts) Int_assoc Un_Int_eq(2) inf.orderI insert_is_Un 
    sumset_empty(2))
  then show "x \<in> stabilizer B" using stabilizer_def[of "B"] assms(1) assms(3) card_subset_eq 
    card_sumset_singleton_subset_eq finite.emptyI finite.insertI finite_Int finite_sumset 
    inf.cobounded2 stabilizer_subset_group subsetD by (smt (verit) mem_Collect_eq)
qed

lemma mem_stabilizer_Un_and_right_imp_left:
  assumes "finite A" and "x \<in> stabilizer (A \<union> B)" and "x \<in> stabilizer B" and "disjnt A B" 
  shows "x \<in> stabilizer A" 
  using mem_stabilizer_Un_and_left_imp_right Un_commute assms disjnt_sym by metis

lemma Union_stabilizer_Class_eq:
  assumes "A \<subseteq> G"
  shows "A = (\<Union> (Class A ` A))" using assms sumset_commute sumset_subgroup_eq_Class_Union 
  sumset_stabilizer_eq_self by presburger

lemma card_stabilizer_sumset_divide_sumset:
  "card (stabilizer (sumset A B)) dvd card (sumset A B)" using card_divide_sumset 
  sumset_commute sumset_stabilizer_eq_self sumset_subset_carrier by metis

lemma card_stabilizer_le:
  assumes "A \<subseteq> G" and "finite A" and "A \<noteq> {}"
  shows "card (stabilizer A) \<le> card A" using assms 
  by (metis card_le_sumset finite.cases insertCI insert_subset stabilizer_finite 
    stabilizer_subset_group sumset_commute sumset_stabilizer_eq_self)

lemma sumset_Inter_subset_sumset:
  assumes "a \<in> G" and "b \<in> G"
  shows "sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C)) \<subseteq> 
    sumset {a \<oplus> b} (stabilizer C)" (is "sumset ?A ?B \<subseteq> _")
proof
  fix x assume "x \<in> sumset ?A ?B"       
  then obtain d1 d2 where "d1 \<in> sumset {a} (stabilizer C)" and
    "d2 \<in> sumset {b} (stabilizer C)" and "x = d1 \<oplus> d2" by (meson IntD2 sumset.cases)
  then obtain c1 c2 where hc1: "c1 \<in> stabilizer C" and hc2: "c2 \<in> stabilizer C" and
    "x = (a \<oplus> c1) \<oplus> (b \<oplus> c2)" using sumset.simps by auto
  then have "x = (a \<oplus> b) \<oplus> (c1 \<oplus> c2)" using hc1 hc2 assms associative commutative 
    stabilizer_subset_group by simp
  thus "x \<in> sumset {a \<oplus> b} (stabilizer C)" using stabilizer_is_subgroup hc1 hc2 
    stabilizer_subset_group sumset.simps sumset_stabilizer_eq assms by blast
qed

subsection\<open>Convergent\<close>

(* I manually exclude the empty set from this definition as its stabilizer is too big *)
definition convergent :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"convergent C A B \<equiv> C \<subseteq> sumset A B \<and> C \<noteq> {} \<and>
  card C + card (stabilizer C) \<ge> card (A \<inter> B) + card (sumset (A \<union> B) (stabilizer C))"

definition convergent_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
"convergent_set A B = Collect (\<lambda> C. convergent C A B)"

lemma convergent_set_sub_powerset:
  "convergent_set A B \<subseteq> Pow (sumset A B)" using convergent_set_def convergent_def by blast

lemma finite_convergent_set:
  assumes "finite A" and "finite B"
  shows "finite (convergent_set A B)"
  using convergent_set_sub_powerset finite_Pow_iff finite_sumset assms finite_subset by metis

subsection\<open>Technical lemmas from DeVos's proof of Kneser's Theorem\<close>

text\<open>The following lemmas correspond to intermediate arguments in the proof of Kneser's Theorem 
by DeVos that we will be following \cite{DeVos_Kneser}. \<close>

lemma stabilizer_sumset_psubset_stabilizer: 
  assumes "a \<in> G" and "b \<in> G" and "A \<inter> sumset {a} (stabilizer C) \<noteq> {}" and 
  "B \<inter> sumset {b} (stabilizer C) \<noteq> {}" and hnotsub: "\<not> sumset {a \<oplus> b} (stabilizer C) \<subseteq> sumset A B"
  shows "stabilizer (sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C))) \<subset> 
    stabilizer C" (is "?H \<subset> _")
proof
  have "sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C)) \<noteq> {}" 
    using assms by (simp add: inf_assoc)
  then show "?H \<subseteq> stabilizer C"
    by (meson assms(1) assms(2) composition_closed subset_stabilizer_of_subset_sumset sumset_Inter_subset_sumset sumset_subset_carrier)
next
  obtain c1 c2 where "a \<oplus> c1 \<in> A" and "b \<oplus> c2 \<in> B" and hc1: "c1 \<in> stabilizer C" and hc2: "c2 \<in> stabilizer C" 
    using assms(1, 2, 3, 4) Left_Coset_eq_sumset_stabilizer by fastforce
  then have hac1mem: "(a \<oplus> c1) \<in> A \<inter> sumset {a} (stabilizer C)" and hac1G: "a \<oplus> c1 \<in> G" and 
    hbc2mem: "(b \<oplus> c2) \<in> B \<inter> sumset {b} (stabilizer C)" and hbc2G: "b \<oplus> c2 \<in> G"
    by (auto simp add: assms(1, 2) sumset.sumsetI)
  have "(a \<oplus> c1) \<oplus> (b \<oplus> c2) \<in> sumset {a \<oplus> b} (stabilizer C)" using assms hc1 hc2
    by (smt (verit) associative commutative composition_closed insertI1 sub sub_composition_closed sumset.sumsetI)
  then have "sumset {a \<oplus> b} (stabilizer C) \<inter>  sumset {(a \<oplus> c1) \<oplus> (b \<oplus> c2)} (stabilizer C) \<noteq> {}" 
    using zero_mem_stabilizer by (smt (verit, ccfv_threshold) composition_closed 
      disjoint_iff_not_equal hac1G hbc2G insertCI right_unit sumset.sumsetI unit_closed)
  then have hsumeq: "sumset {a \<oplus> b} (stabilizer C) = sumset {(a \<oplus> c1) \<oplus> (b \<oplus> c2)} (stabilizer C)" 
    using sumset_stabilizer_eq_iff assms hac1G hbc2G composition_closed by presburger
  have "(sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C))) \<subseteq> sumset {a \<oplus> b} (stabilizer C)"
    by (simp add: assms(1, 2) sumset_Inter_subset_sumset)
  have hsummem: "(a \<oplus> c1) \<oplus> (b \<oplus> c2) \<in> sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C))" 
    using hac1mem hbc2mem hac1G hbc2G sumset.sumsetI by blast
  show "?H \<noteq> stabilizer C"
    using stabilizer_neq_subset_sumset[OF _ hsummem] hnotsub hsumeq sumset_Inter_subset_sumset assms 
      sumset_subset_carrier composition_closed sumset_mono sumset.sumsetI zero_mem_stabilizer 
      inf.cobounded1 right_unit unit_closed by metis
qed

lemma stabilizer_eq_stabilizer_union: 
  assumes "a \<in> G" and "b \<in> G" and"A \<inter> sumset {a} (stabilizer C) \<noteq> {}" and 
  "B \<inter> sumset {b} (stabilizer C) \<noteq> {}" and hnotsub: "\<not> sumset {a \<oplus> b} (stabilizer C) \<subseteq> sumset A B" and 
  "C \<subseteq> sumset A B" and "finite C" and
  "C \<inter> sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C)) = {}" and "C \<noteq> {}" and
  "finite A" and "finite B"
  shows "stabilizer (sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C))) = 
    stabilizer (C \<union> sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C)))" (is "stabilizer ?H = stabilizer ?K")
proof
  show "stabilizer ?H \<subseteq> stabilizer ?K" using subset_stabilizer_Un Int_absorb1 
    stabilizer_sumset_psubset_stabilizer psubset_imp_subset assms by metis
next
  have hCG : "C \<subseteq> G" using assms(6) sumset_subset_carrier by force
  show "stabilizer ?K \<subseteq> stabilizer ?H"
  proof
    fix x assume hxC1: "x \<in> stabilizer ?K"
    moreover have "x \<in> stabilizer C"
    proof-
      have hC_Un: "C = (\<Union> (Class C ` C))" using Union_stabilizer_Class_eq hCG by simp
      have hCsumx: "sumset {x} C = (\<Union> y \<in> Class C ` C. sumset {x} y)" 
      proof
        show "sumset {x} C \<subseteq> \<Union> (sumset {x} ` Class C ` C)"
        proof
          fix y assume hy: "y \<in> sumset {x} C"
          then obtain c where hc: "c \<in> C" and hyxc: "y = x \<oplus> c" using sumset.cases by blast
          then obtain K where hK: "K \<in> Class C ` C" and "c \<in> K" using hC_Un by blast    
          then have "y \<in> sumset {x} K" using hyxc hc by (metis sumset.cases
            sumset.sumsetI hCG hy singletonD subset_iff)
          then show "y \<in> \<Union> (sumset {x} ` Class C ` C)" using hK by auto
      qed
      next
        show "\<Union> (sumset {x} ` Class C ` C) \<subseteq> sumset {x} C" 
        proof(intro Union_least)
          fix X assume "X \<in> sumset {x} ` Class C ` C"
          then obtain K where "K \<in> Class C ` C" and "X = sumset {x} K" by blast
          then show "X \<subseteq> sumset {x} C" using sumset_mono[of "{x}" "{x}" "K" "C"] 
            hC_Un subset_refl by blast
        qed
      qed
      have "x \<notin> stabilizer C \<Longrightarrow> False" 
      proof-
      assume hxC: "x \<notin> stabilizer C"
      then have hxG: "x \<in> G" using hxC1 stabilizer_subset_group by blast
      then have hxCne: "sumset {x} C \<noteq> C" using stabilizer_def[of "C"] hCG Int_absorb2 
        hxC by (metis (mono_tags, lifting) mem_Collect_eq)
      moreover have hxsplit: "sumset {x} C \<union> sumset {x} ?H = C \<union> ?H" 
        using hxC1 stabilizer_def[of "?K"] sumset_subset_carrier assms(6) sumset_subset_Un2 by force
      have "sumset {x} C \<inter> ?H \<noteq> {}" 
      proof
        assume "sumset {x} C \<inter> ?H = {}"
        then have "sumset {x} C \<subset> C" using hxsplit hxCne by blast
        thus "False" using hCG assms(6) assms(7) hxC1 stabilizer_subset_group psubset_card_mono 
          by (metis card_sumset_singleton_eq sumset_Int_carrier sumset_commute 
          sumset_stabilizer_eq_self hxG less_irrefl_nat)
        qed
      then obtain c where hc: "c \<in> C" and 
        hxcne: "sumset {x} (Class C c) \<inter> ?H \<noteq> {}" using hCsumx by blast
      then have hxc: "sumset {x} (Class C c) = Class C (x \<oplus> c)" 
        using hxG assms(6) Left_Coset_Class_unit Left_Coset_eq_sumset_stabilizer sumset_assoc 
        sumset_singletons_eq composition_closed sumset.cases sumset_stabilizer_eq_self hCG by (smt (verit))
      have hClassCempty: "Class C (x \<oplus> c) \<inter> C = {}" 
      proof-
        have "\<not> Class C (x \<oplus> c) \<subseteq> C" using hxc hxcne assms(8) by blast
        then show ?thesis using Class_cover_imp_subset_or_disj[OF hC_Un _ hCG] 
          by (meson composition_closed hCG hc hxG subsetD)
      qed
      have "Class C (x \<oplus> c) \<subseteq> sumset {x} C" using hCsumx hc hxc by blast
      then have "Class C (x \<oplus> c) \<subseteq> ?H" using hClassCempty hxsplit by auto
      moreover have "card (Class C (x \<oplus> c)) = card (stabilizer C)" using hxG hc hCG 
        composition_closed Right_Coset_Class_unit Right_Coset_cardinality sumset_Int_carrier
        Class_cover_imp_subset_or_disj assms by auto
      ultimately have "card (stabilizer C) \<le> card ?H" using card_mono finite_sumset assms(10, 11) finite_Int by metis
      moreover have "card ?H < card (sumset {a \<oplus> b} (stabilizer C))"
      proof (intro psubset_card_mono psubsetI sumset_Inter_subset_sumset assms(1) assms(2))
        show "finite (sumset {a \<oplus> b} (stabilizer C))"
          using stabilizer_finite assms finite_sumset by (simp add: hCG)
      next
        show "?H \<noteq> sumset {a \<oplus> b} (stabilizer C)" 
          using hnotsub sumset_mono by (metis Int_lower1)
      qed
      ultimately show "False" 
        using assms(1, 2) stabilizer_subset_group by (simp add: card_sumset_singleton_subset_eq)  
      qed
      then show ?thesis by auto
    qed
    moreover have "finite ?H" using finite_sumset assms(10, 11) finite_Int by simp
    ultimately show "x \<in> stabilizer ?H" using mem_stabilizer_Un_and_right_imp_left[of "?H" "x" "C"]
      disjnt_def assms Un_commute by (metis disjoint_iff_not_equal)
  qed
qed

lemma sumset_inter_ineq: 
  assumes "B \<inter> sumset {a} (stabilizer C) = {}" and "stabilizer (sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C))) \<subset> stabilizer C" and
  "a \<in> A" and "a \<in> G" and "finite A" and "finite B" and "A \<noteq> {}" and "B \<noteq> {}" and "finite (stabilizer C)"
  shows "int (card (sumset (A \<union> B) (stabilizer C))) - card (sumset (A \<union> B) (stabilizer (sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C))))) \<ge> 
    int (card (stabilizer C)) - card (sumset (A \<inter> sumset {a} (stabilizer C)) (stabilizer (sumset (A \<inter> sumset {a} (stabilizer C)) (B \<inter> sumset {b} (stabilizer C)))))"
  (is "int (card (sumset (A \<union> B) (stabilizer C))) - card (sumset (A \<union> B) ?H1) \<ge> 
                int (card (stabilizer C)) - card (sumset ?A1 ?H1)")
proof-
  have hfinsumH1:"finite (sumset (A \<union> B) ?H1)" 
    using finite_sumset assms by (meson finite_Un psubsetE rev_finite_subset)
  have hsubsumH1: "sumset (A \<union> B) ?H1 \<subseteq> sumset (A \<union> B) (stabilizer C)" 
    using sumset.cases assms by (meson psubsetE subset_refl sumset_mono)
  have hsumH1card_le: "card (sumset (A \<union> B) ?H1) \<le> card (sumset (A \<union> B) (stabilizer C))"
    using card_mono finite_sumset stabilizer_finite assms
    by (metis equalityE finite_UnI psubset_imp_subset sumset_mono)
  have hsub: "sumset ?A1 ?H1 \<subseteq> sumset {a} (stabilizer C)"
  proof
    fix x assume "x \<in> sumset ?A1 ?H1"
    then obtain h1 f where "h1 \<in> ?A1" and hf: "f \<in> ?H1" and 
      hx: "x = h1 \<oplus> f" by (meson sumset.cases)
    then obtain c where hc: "c \<in> stabilizer C" and hac: "h1 = a \<oplus> c"
      by (metis Int_iff empty_iff insert_iff sumset.cases)
    then have hcf: "c \<oplus> f \<in> stabilizer C" using hf assms(2) stabilizer_is_subgroup 
      subgroup_def monoid_axioms Group_Theory.group.axioms(1) 
      Group_Theory.monoid_def subset_iff psubset_imp_subset
      by (smt (verit) stabilizer_subset_group sumset.sumsetI sumset_stabilizer_eq)
    have hcG: "c \<in> G" using hc stabilizer_subset_group by auto 
    have hfG: "f \<in> G" using hf stabilizer_subset_group by auto
    show "x \<in> sumset {a} (stabilizer C)" using hx hac assms stabilizer_subset_group hcf
      using Left_Coset_eq_sumset_stabilizer Left_Coset_memI associative hcG hfG by presburger
  qed
  moreover have "finite (sumset ?A1 ?H1)" using finite_sumset assms stabilizer_finite finite_subset
    by (metis finite.simps hsub)
  ultimately have "card (sumset {a} (stabilizer C)) - card (sumset ?A1 ?H1) = 
    card (sumset {a} (stabilizer C) - sumset ?A1 ?H1)"
    using card_Diff_subset by metis
  moreover have "card (sumset ?A1 ?H1) \<le>  card (sumset {a} (stabilizer C))"
    using card_mono hsub finite_sumset assms by (metis finite.simps)
  ultimately have "int (card (sumset {a} (stabilizer C))) - card (sumset ?A1 ?H1) = 
    card (sumset {a} (stabilizer C) - sumset ?A1 ?H1)" by linarith
  also have "... \<le> card ((sumset (A \<union> B) (stabilizer C)) - (sumset (A \<union> B) ?H1))"
  proof-
    have "sumset {a} (stabilizer C) - sumset ?A1 ?H1 \<subseteq> sumset (A \<union> B) (stabilizer C) - sumset (A \<union> B) ?H1"
    proof
      fix x assume hx: "x \<in> sumset {a} (stabilizer C) - sumset ?A1 ?H1"
      then obtain c where hxac: "x = a \<oplus> c" and hc: "c \<in> stabilizer C" and hcG: "c \<in> G" 
        using sumset.cases by blast
      then have "x \<in> sumset (A \<union> B) (stabilizer C)" using assms sumset.cases by blast
      moreover have "x \<notin> sumset (A \<union> B) ?H1"
      proof
        assume "x \<in> sumset (A \<union> B) ?H1"
        then obtain y h1 where hy: "y \<in> A \<union> B" and hyG: "y \<in> G" and hh1G: "h1 \<in> G" 
          and hh1: "h1 \<in> ?H1" and hxy: "x = y \<oplus> h1" by (meson sumset.cases)
        then have "y = a \<oplus> (c \<oplus> inverse h1)" using hxac hxy assms associative commutative composition_closed
          inverse_closed invertible invertible_left_inverse2 by (metis hcG)
        moreover have "h1 \<in> stabilizer C" using hh1 assms by auto
        moreover hence "c \<oplus> inverse h1 \<in> stabilizer C" using hc stabilizer_is_subgroup subgroup_def
          group_axioms invertible subgroup.subgroup_inverse_iff submonoid.sub_composition_closed hh1G by metis
        ultimately have "y \<in> sumset {a} (stabilizer C)" 
          using assms hcG hh1G by blast
        moreover hence "y \<in> A" using assms(1) hy by auto
        ultimately have "x \<in> sumset ?A1 ?H1" using hxy hh1
          by (simp add: hyG hh1G sumset.sumsetI)
        thus "False" using hx by auto
      qed
      ultimately show "x \<in> sumset (A \<union> B) (stabilizer C) - sumset (A \<union> B) ?H1" 
        by simp
    qed
    thus ?thesis using card_mono finite_Diff finite_sumset assms 
      by (metis finite_UnI nat_int_comparison(3))
  qed
  also have "... = int (card (sumset (A \<union> B) (stabilizer C))) - 
    card (sumset (A \<union> B) ?H1)"
    using card_Diff_subset[OF hfinsumH1 hsubsumH1] hsumH1card_le by linarith
  finally show "int (card (sumset (A \<union> B) (stabilizer C))) - card (sumset (A \<union> B) ?H1) \<ge> 
    int (card (stabilizer C)) - card (sumset ?A1 ?H1)" 
    using assms by (metis card_sumset_singleton_subset_eq stabilizer_subset_group)
qed

lemma exists_convergent_min_stabilizer:
  assumes hind: "\<forall>m<n. \<forall>C D. C \<subseteq> G \<longrightarrow> D \<subseteq> G \<longrightarrow> finite C \<longrightarrow> finite D \<longrightarrow> C \<noteq> {} \<longrightarrow>
    D \<noteq> {} \<longrightarrow> card (sumset C D) + card C = m \<longrightarrow> 
    card (sumset C (stabilizer (sumset C D))) + card (sumset D (stabilizer (sumset C D))) - 
    card ((stabilizer (sumset C D)))
    \<le> card (sumset C D)" and hAG: "A \<subseteq> G" and hBG: "B \<subseteq> G" and hA: "finite A" and 
    hB: "finite B" and hAne: "A \<noteq> {}" and "A \<inter> B \<noteq> {}" and
    hcardsum: "card (sumset A B) + card A = n" and hintercardA: "card (A \<inter> B) < card A"
  obtains X where "convergent X A B" and "\<And> Y. Y \<in> convergent_set A B \<Longrightarrow> 
    card (stabilizer Y) \<ge> card (stabilizer X)"
proof-
  let ?C0 = "sumset (A \<inter> B) (A \<union> B)"
  have hC0ne: "?C0 \<noteq> {}" using assms by fast
  moreover have "finite ?C0" using sumset_inter_union_subset finite_sumset assms by auto
  ultimately have "finite (stabilizer ?C0)" using stabilizer_finite
    using sumset_subset_carrier by presburger
  then have hcard_sumset_le: "card (A \<inter> B) \<le> card (sumset (A \<inter> B) (stabilizer ?C0))" 
    using card_le_sumset sumset_commute sub_unit_closed assms
    by (metis Int_Un_eq(3) Un_subset_iff finite_Int unit_closed)
  have "card ?C0 \<le> card (sumset A B)" 
    using card_mono sumset_inter_union_subset finite_sumset assms
    by (simp add: card_mono finite_sumset hA hB sumset_inter_union_subset)
  then have "card ?C0 + card (A \<inter> B) < card (sumset A B) + card A" 
    using hintercardA by auto
  then obtain m where "m < n" and "card ?C0 + card (A \<inter> B) = m" using hcardsum by auto
  then have "card (sumset (A \<inter> B) (stabilizer ?C0)) + 
    card (sumset (A \<union> B) (stabilizer ?C0)) - card (stabilizer ?C0) \<le> card ?C0"
  using assms finite_Un finite_Int
    by (metis Int_Un_eq(4) Un_empty Un_subset_iff)
  then have "card ?C0 + card (stabilizer ?C0) \<ge> 
    card (A \<inter> B) + card (sumset (A \<union> B) (stabilizer ?C0))" using hcard_sumset_le 
    by auto
  then have "?C0 \<in> convergent_set A B" using convergent_set_def convergent_def 
   sumset_inter_union_subset hC0ne by auto
  then have hconvergent_ne: "convergent_set A B \<noteq> {}" by auto
  define KS where "KS \<equiv> (\<lambda> X. card (stabilizer X)) ` convergent_set A B"
  define K where "K \<equiv> Min KS"
  define C where "C \<equiv> @C. C \<in> convergent_set A B \<and> K = card (stabilizer C)"
  obtain KS: "finite KS" "KS \<noteq> {}" 
   using hconvergent_ne finite_convergent_set assms KS_def by auto
  then have "K \<in> KS" using K_def Min_in by blast
  then have "\<exists> X. X \<in> convergent_set A B \<and> K = card (stabilizer X)" 
   using KS_def by auto
  then obtain "C \<in> convergent_set A B" and Keq: "K = card (stabilizer C)" 
    by (metis (mono_tags, lifting) C_def someI_ex)
  then have hC: "C \<subseteq> sumset A B" and hCne: "C \<noteq> {}" and
    hCcard: "card C + card (stabilizer C) \<ge> 
    card (A \<inter> B) + card (sumset (A \<union> B) (stabilizer C))"
  using convergent_set_def convergent_def by auto
  have hCmin: "\<And> Y. Y \<in> convergent_set A B \<Longrightarrow> 
    card (stabilizer Y) \<ge> card (stabilizer C)" 
    using K_def KS_def Keq Min_le KS(1) by auto
  show ?thesis using hCmin hC hCcard hCne local.convergent_def that by presburger
qed

end

context normal_subgroup
begin

subsection\<open> A function that picks coset representatives randomly\<close>

definition \<phi> :: "'a set \<Rightarrow> 'a" where 
  "\<phi> = (\<lambda> x. if x \<in> G // K then (SOME a. a \<in> G \<and> x = a \<cdot>| K) else undefined)"

definition quot_comp_alt :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where "quot_comp_alt a b = \<phi> ((a \<cdot> b) \<cdot>| K)"

lemma phi_eq_coset:
  assumes "\<phi> x = a" and "a \<in> G" and "x \<in> G // K"
  shows "x = a \<cdot>| K"
proof-
  have "(SOME a. a \<in> G \<and> x = a \<cdot>| K) = a" using \<phi>_def assms by simp
  then show ?thesis using some_eq_ex representant_exists Left_Coset_Class_unit assms
    by (metis (mono_tags, lifting))
qed

lemma phi_coset_mem:
  assumes "a \<in> G"
  shows "\<phi> (a \<cdot>| K) \<in> a \<cdot>| K"
proof-
  obtain x where hx: "x = \<phi> (a \<cdot>| K)" by auto
  then have "x = (SOME x. x \<in> G \<and> a \<cdot>| K = x \<cdot>| K)" using \<phi>_def assms 
    Class_in_Partition Left_Coset_Class_unit by presburger
  then show ?thesis using \<phi>_def Class_self Left_Coset_Class_unit hx assms 
    by (smt (verit, ccfv_SIG) tfl_some)
qed

lemma phi_coset_eq: 
  assumes "a \<in> G" and "\<phi> x = a" and "x \<in> G // K"
  shows "\<phi> (a \<cdot>| K) = a" using phi_eq_coset assms by metis

lemma phi_inverse_right:
  assumes "g \<in> G"
  shows "quot_comp_alt g (\<phi> (inverse g \<cdot>| K)) = \<phi> K"
proof-
  have "g \<cdot> (\<phi> (inverse g \<cdot>| K)) \<in> (g \<cdot> (inverse g) \<cdot>| K)" 
    using phi_coset_mem assms by (smt (z3) Left_Coset_memE factor_unit invertible invertible_right_inverse 
    invertible_inverse_closed invertible_inverse_inverse sub invertible_left_inverse2)
  then have "g \<cdot> (\<phi> (inverse g \<cdot>| K)) \<cdot>| K = K"
    using Block_self Left_Coset_Class_unit Normal_def quotient.unit_closed sub
    by (metis assms composition_closed invertible invertible_inverse_closed invertible_right_inverse)
  then show ?thesis using quot_comp_alt_def by auto
qed

lemma phi_inverse_left:
  assumes "g \<in> G"
  shows "quot_comp_alt (\<phi> (inverse g \<cdot>| K)) g = \<phi> K"
proof-
  have "(\<phi> (inverse g \<cdot>| K)) \<cdot> g \<in> ((inverse g) \<cdot> g) \<cdot>| K" using phi_coset_mem assms
    by (metis Left_Coset_memE factor_unit invertible invertible_inverse_closed invertible_left_inverse normal)
  then have "(\<phi> (inverse g \<cdot>| K)) \<cdot> g \<cdot>| K = K" using Block_self Left_Coset_Class_unit Normal_def 
    quotient.unit_closed sub by (smt (verit, best) assms composition_closed invertible invertible_inverse_closed
    invertible_left_inverse)
  then show ?thesis using quot_comp_alt_def by auto
qed

lemma phi_mem_coset_eq:
  assumes "a \<in> G // K" and "b \<in> G"
  shows "\<phi> a \<in> b \<cdot>| K  \<Longrightarrow> a = (b \<cdot>| K)"
proof-
  assume "\<phi> a \<in> b \<cdot>| K"
  then have "a \<inter> (b \<cdot>| K) \<noteq> {}"
    by (metis Class_closed Class_is_Left_Coset Int_iff assms empty_iff phi_coset_mem phi_eq_coset)
  then show "a = b \<cdot>| K" by (metis Class_in_Partition Class_is_Left_Coset assms disjoint)
qed


lemma forall_unique_repr: 
  "\<forall> x \<in> G // K. \<exists>! k \<in> \<phi> ` (G // K). x = k \<cdot>| K" 
proof    
  fix x assume hx: "x \<in> G // K"
  then have "\<phi> x \<cdot>| K = x"
    by (metis Class_is_Left_Coset block_closed phi_coset_mem phi_eq_coset representant_exists)
  then have hex: "\<exists> k \<in> \<phi> ` (G // K). x = k \<cdot>| K" using hx by blast
  moreover have "\<And> a b. a \<in> \<phi> ` (G // K) \<Longrightarrow> x = a \<cdot>| K \<Longrightarrow> b \<in> \<phi> ` (G // K) \<Longrightarrow> x = b \<cdot>| K \<Longrightarrow> 
    a = b"
  proof-
    fix a b assume "a \<in> \<phi> ` (G // K)" and hxa: "x = a \<cdot>| K" and "b \<in> \<phi> ` (G // K)" and 
      hxb: "x = b \<cdot>| K"
    then obtain z w where "a = \<phi> (z \<cdot>| K)" and "b = \<phi> (w \<cdot>| K)" and "z \<in> G" and "w \<in> G" 
      using representant_exists Left_Coset_Class_unit by force
    then show "a = b" using hxa hxb 
      by (metis Class_in_Partition Class_is_Left_Coset block_closed phi_coset_mem phi_eq_coset)
  qed
  ultimately show "\<exists>! k \<in> \<phi> ` (G // K). x = k \<cdot>| K" by blast
qed

lemma phi_inj_on:
  shows "inj_on \<phi> (G // K)"
proof(intro inj_onI)
  fix x y assume "x \<in> G // K" and hy: "y \<in> G // K" and hxy: "\<phi> x = \<phi> y"
  then obtain a b where "x = a \<cdot>| K" and "y = b \<cdot>| K" and "a \<in> G" and "b \<in> G" 
    using representant_exists Left_Coset_Class_unit by metis
  then show "x = y" using hxy hy by (metis phi_coset_mem phi_mem_coset_eq)
qed

lemma phi_coset_eq_self:
  assumes "a \<in> G // K"
  shows "\<phi> a \<cdot>| K = a"
  by (metis Class_closed Class_is_Left_Coset assms phi_coset_mem phi_eq_coset representant_exists)

lemma phi_coset_comp_eq:
  assumes "a \<in> G // K" and "b \<in> G // K"
  shows "\<phi> a \<cdot> \<phi> b \<cdot>| K = a [\<cdot>] b" using assms phi_coset_eq_self
  by (metis Class_is_Left_Coset block_closed factor_composition phi_coset_mem representant_exists)

lemma phi_comp_eq:
  assumes "a \<in> G // K" and "b \<in> G // K"
  shows "\<phi> (a [\<cdot>] b) = quot_comp_alt (\<phi> a) (\<phi> b)"
  using phi_coset_comp_eq quot_comp_alt_def assms by auto

lemma phi_image_subset:
  "\<phi> ` (G // K) \<subseteq> G"
proof(intro image_subsetI, simp add: \<phi>_def)
    fix x assume "x \<in> G // K"
    then show "(SOME a. a \<in> G \<and> x = a \<cdot>| K) \<in> G" 
      using Left_Coset_Class_unit representant_exists someI_ex by (metis (mono_tags, lifting))
qed

lemma phi_image_group:
  "Group_Theory.group (\<phi> ` (G // K)) quot_comp_alt (\<phi> K)"
proof-
  have hmonoid: "Group_Theory.monoid (\<phi> ` (G // K)) quot_comp_alt (\<phi> K)"
  proof
    show "\<And>a b. a \<in> \<phi> ` (G // K) \<Longrightarrow> b \<in> \<phi> ` (G // K) \<Longrightarrow>
      quot_comp_alt a b \<in> \<phi> ` (G // K)" using quot_comp_alt_def imageI phi_image_subset
      by (metis Class_in_Partition Left_Coset_Class_unit composition_closed subset_iff)
    next
      show "(\<phi> K) \<in> \<phi> ` (G // K)" using \<phi>_def Left_Coset_Class_unit imageI Normal_def by blast
    next
      show "\<And>a b c. a \<in> \<phi> ` Partition \<Longrightarrow> b \<in> \<phi> ` Partition \<Longrightarrow> c \<in> \<phi> ` Partition \<Longrightarrow> 
        quot_comp_alt (quot_comp_alt a b) c = quot_comp_alt a (quot_comp_alt b c)" 
      proof-
        fix a b c assume ha: "a \<in> \<phi> ` (G // K)" and hb: "b \<in> \<phi> ` (G // K)" and hc: "c \<in> \<phi> ` (G // K)"
        have habc: "a \<cdot> b \<cdot> c \<in> G" using ha hb hc composition_closed phi_image_subset by (meson subsetD)
        have hab: "quot_comp_alt a b \<in> (a \<cdot> b) \<cdot>| K" using phi_image_subset quot_comp_alt_def ha hb
          by (metis composition_closed phi_coset_mem subsetD)
        then have "quot_comp_alt (quot_comp_alt a b) c \<in> (a \<cdot> b \<cdot> c) \<cdot>| K" using quot_comp_alt_def phi_image_subset ha hb hc 
          by (smt (z3) Block_self Class_closed Class_in_Partition Left_Coset_Class_unit composition_closed 
          natural.commutes_with_composition phi_coset_mem subset_iff)
        moreover have hbc: "quot_comp_alt b c \<in> (b \<cdot> c) \<cdot>| K" using hb hc phi_image_subset quot_comp_alt_def
          by (metis composition_closed phi_coset_mem subset_iff)
        moreover hence "quot_comp_alt a (quot_comp_alt b c) \<in> (a \<cdot> b \<cdot> c) \<cdot>| K" using quot_comp_alt_def phi_image_subset ha hb hc
          by (smt (verit, del_insts) Block_self Class_closed Class_in_Partition Left_Coset_Class_unit 
          associative composition_closed natural.commutes_with_composition phi_coset_mem subset_iff)
        moreover have "a \<cdot> (quot_comp_alt b c) \<cdot>| K \<in> G // K" using ha hb hc phi_image_subset
          by (metis Class_closed Class_in_Partition Class_is_Left_Coset hbc composition_closed in_mono subset_eq)
        moreover have "(quot_comp_alt a b) \<cdot> c \<cdot>| K \<in> G // K" using ha hb hc phi_image_subset
          by (metis Class_closed Class_in_Partition Left_Coset_Class_unit hab composition_closed in_mono)
        ultimately show "quot_comp_alt (quot_comp_alt a b) c = quot_comp_alt a (quot_comp_alt b c)"
          using phi_mem_coset_eq[OF _ habc] quot_comp_alt_def by metis
      qed
    next
      show "\<And>a. a \<in> \<phi> ` Partition \<Longrightarrow> quot_comp_alt (\<phi> K) a = a" using quot_comp_alt_def \<phi>_def
        phi_image_subset image_iff phi_coset_eq subsetD by (smt (z3) Normal_def Partition_def 
        natural.image.sub_unit_closed phi_comp_eq quotient.left_unit)
    next
      show "\<And>a. a \<in> \<phi> ` Partition \<Longrightarrow> quot_comp_alt a (\<phi> K) = a" using quot_comp_alt_def \<phi>_def
        phi_image_subset image_iff phi_coset_eq subsetD by (smt (verit) Normal_def 
        factor_composition factor_unit normal_subgroup.phi_coset_eq_self normal_subgroup_axioms 
        quotient.unit_closed right_unit unit_closed)
  qed
  moreover show "Group_Theory.group (\<phi> ` (G // K)) quot_comp_alt (\<phi> K)"
  proof(simp add: group_def group_axioms_def hmonoid)
    show "\<forall>u. u \<in> \<phi> ` Partition \<longrightarrow> monoid.invertible (\<phi> ` Partition) quot_comp_alt (\<phi> K) u"
    proof(intro allI impI)
      fix g assume hg: "g \<in> \<phi> ` (G // K)"
      then have "quot_comp_alt g (\<phi> ((inverse g) \<cdot>| K)) = (\<phi> K)" 
        and "quot_comp_alt (\<phi> ((inverse g) \<cdot>| K)) g = (\<phi> K)"
        using phi_image_subset phi_inverse_right phi_inverse_left by auto
      moreover have "\<phi> ((inverse g) \<cdot>| K) \<in> \<phi> ` (G // K)" using imageI hg phi_image_subset
        by (metis (no_types, opaque_lifting) Class_in_Partition Left_Coset_Class_unit in_mono 
        invertible invertible_inverse_closed)
      ultimately show "monoid.invertible (\<phi> ` Partition) quot_comp_alt (\<phi> K) g"
        using monoid.invertibleI[OF hmonoid] hg by presburger
    qed
  qed
qed

lemma phi_map: "Set_Theory.map \<phi> Partition (\<phi> ` Partition)"
  by (auto simp add: Set_Theory.map_def \<phi>_def)

lemma phi_image_isomorphic:
  "group_isomorphism \<phi> (G // K) ([\<cdot>]) (Class \<one>) (\<phi> ` (G // K)) quot_comp_alt (\<phi> K)"
proof - 
  have "bijective_map \<phi> Partition (\<phi> ` Partition)" 
    using bijective_map_def bijective_def bij_betw_def phi_inj_on phi_map by blast
  moreover have "Group_Theory.monoid (\<phi> ` Partition) quot_comp_alt (\<phi> K)" 
    using phi_image_group group_def by metis
  moreover have "\<phi> (Class \<one>) = \<phi> K" using Left_Coset_Class_unit Normal_def by auto
  ultimately show ?thesis
    by (auto simp add: group_isomorphism_def group_homomorphism_def monoid_homomorphism_def 
    phi_image_group quotient.monoid_axioms quotient.group_axioms monoid_homomorphism_axioms_def 
    phi_comp_eq phi_map)
qed

end

context subgroup_of_additive_abelian_group

begin

lemma Union_Coset_card_eq:
  assumes hSG: "S \<subseteq> G" and hSU: "(\<Union> (Class ` S)) = S"   
  shows "card S = card H * card (Class ` S)"
proof(cases "finite H")
  case hH: True
  have hfin: "\<And>A. A \<in> Class ` S \<Longrightarrow> finite A" using hSG Right_Coset_Class_unit 
    Right_Coset_cardinality hH card_eq_0_iff empty_iff sub_unit_closed subsetD
    by (smt (verit, del_insts) imageE)
  have "card S = card H * card (Class ` S)" when hS: "finite S"
  proof-
    have hdisj: "pairwise (\<lambda>s t. disjnt s t) (Class ` S)"
    proof (intro pairwiseI)
      fix x y assume "x \<in> Class ` S" and "y \<in> Class ` S" and hxy: "x \<noteq> y"
      then obtain a b where "x = Class a" and "y = Class b" and 
        "a \<in> S" and "b \<in> S" by blast
      then show "disjnt x y" using disjnt_def hxy 
        by (smt (verit, ccfv_threshold) not_disjoint_implies_equal hSG subsetD)
    qed
    then have "card (\<Union> (Class ` S)) = sum card (Class ` S)" using card_Union_disjoint hfin by blast
    moreover have "finite (Class ` S)" using hS by blast
    ultimately have "card (\<Union> (Class ` S)) = (\<Sum> a \<in> Class ` S. card a)" 
      using sum_card_image hdisj by blast
    moreover have "\<And> a. a \<in> Class ` S \<Longrightarrow> card a = card H" 
      using hSG Right_Coset_Class_unit Right_Coset_cardinality by auto
    ultimately show "card S = card H * card (Class ` S)" 
      using hSU by simp
  qed
  moreover have "card S = card H * card (Class ` S)" when hS: "\<not> finite S"
    using finite_Union hfin hS hSU by (metis card_eq_0_iff mult_0_right)
  ultimately show ?thesis by blast
next
  case hH: False
  have "card S = card H * card (Class ` S)" when "S = {}"
    by (simp add: that)
  then have hinf: "\<And> A. A \<in> Class ` S \<Longrightarrow> infinite A" using hSG Right_Coset_Class_unit 
    Right_Coset_cardinality hH card_eq_0_iff empty_iff sub_unit_closed subsetD
    by (smt (verit) Class_self imageE)
  moreover have "card S = card H * card (Class ` S)" when "S \<noteq> {}" using hSU by (metis Class_closed2 
    Normal_def card.infinite card_sumset_0_iff hH hSG mult_is_0 sumset_subgroup_eq_Class_Union unit_closed)
  ultimately show ?thesis by fastforce
qed

end

context subgroup_of_abelian_group
begin

interpretation GH: additive_abelian_group "G // H" "([\<cdot>])" "Class \<one>"
proof
  fix x y assume "x \<in> G // H" and "y \<in> G // H"
  then show "x [\<cdot>] y = y [\<cdot>] x" using Class_commutes_with_composition commutative representant_exists 
    by metis
qed

interpretation GH_repr: additive_abelian_group "\<phi> ` (G // H)" "quot_comp_alt" "\<phi> H"
proof(simp add: additive_abelian_group_def abelian_group_def phi_image_group 
  commutative_monoid_def commutative_monoid_axioms_def, intro conjI allI impI)
  show "Group_Theory.monoid (\<phi> ` Partition) quot_comp_alt (\<phi> H)" 
    using phi_image_group group_def by metis
next
  show "\<And> x y. x \<in> \<phi> ` Partition \<Longrightarrow> y \<in> \<phi> ` Partition \<Longrightarrow> quot_comp_alt x y = quot_comp_alt y x"
    by (auto) (metis GH.commutative phi_comp_eq)
qed

lemma phi_image_sumset_eq:
  assumes "A \<subseteq> G // H" and "B \<subseteq> G // H"
  shows "\<phi> ` (GH.sumset A B) = GH_repr.sumset (\<phi> ` A) (\<phi> ` B)"
proof(intro subset_antisym image_subsetI subsetI)
  fix x assume "x \<in> GH.sumset A B"
  then obtain c d where "x = quotient_composition c d" and hc: "c \<in> A" and hd: "d \<in> B" 
    using GH.sumset.cases by blast
  then have "\<phi> x = quot_comp_alt (\<phi> c) (\<phi> d)" 
    using phi_comp_eq assms subsetD by blast
  then show "\<phi> x \<in> GH_repr.sumset (\<phi> ` A) (\<phi> ` B)" 
    using hc hd assms subsetD GH_repr.sumsetI imageI by auto
next
  fix x assume "x \<in> GH_repr.sumset (\<phi> ` A) (\<phi> ` B)"
  then obtain a b where "x = quot_comp_alt a b" and ha: "a \<in> \<phi> ` A" and hb: "b \<in> \<phi> ` B" 
    using GH_repr.sumset.cases by metis
  moreover obtain c d where "a = \<phi> c" and "b = \<phi> d" and "c \<in> A" and "d \<in> B" 
    using ha hb by blast
  ultimately show "x \<in> \<phi> ` GH.sumset A B" using phi_comp_eq assms imageI GH.sumsetI
    by (smt (verit, del_insts) subsetD)
qed

lemma phi_image_stabilizer_eq:
  assumes "A \<subseteq> G // H"
  shows "\<phi> ` (GH.stabilizer A) = GH_repr.stabilizer (\<phi> ` A)"
proof(intro subset_antisym image_subsetI subsetI)
  fix x assume "x \<in> GH.stabilizer A"
  then have "GH.sumset {x} A = A" and hx: "x \<in> G // H" using GH.stabilizer_def assms by auto
  then have "GH_repr.sumset (\<phi> ` {x}) (\<phi> ` A) = \<phi> ` A" using assms phi_image_sumset_eq
    by (metis empty_subsetI insert_subset)
  then show "\<phi> x \<in> GH_repr.stabilizer (\<phi> ` A)" using GH_repr.stabilizer_def assms
    by (smt (z3) GH_repr.sumset_Int_carrier hx image_empty image_eqI image_insert mem_Collect_eq)
next
  fix x assume "x \<in> GH_repr.stabilizer (\<phi> ` A)"
  then have hstab: "GH_repr.sumset {x} (\<phi> ` A) = (\<phi> ` A)" and hx: "x \<in> \<phi> ` (G // H)" 
    using GH_repr.stabilizer_def assms phi_image_subset by auto
  then obtain B where hB: "B \<in> G // H" and hBx: "\<phi> B = x" by blast
  then have "GH_repr.sumset (\<phi> ` {B}) (\<phi> ` A) = \<phi> ` A" using hstab by auto
  then have "GH.sumset {B} A = A" using phi_image_sumset_eq phi_inj_on assms hB
    GH.sumset_subset_carrier by (smt (z3) GH.sumset_singletons_eq inj_on_image_eq_iff 
    quotient.right_unit quotient.unit_closed)
  then show "x \<in> \<phi> ` (GH.stabilizer A)" using assms hBx GH.stabilizer_def
    by (smt (z3) GH.sumset_Int_carrier hB image_iff mem_Collect_eq)
qed

end

subsection\<open>Useful group-theoretic results\<close>

lemma residue_group: "abelian_group {0..(m :: nat)-1} (\<lambda> x y. ((x + y) mod m)) (0 :: int)"
proof(cases "m > 1")
  case hm: True
  then have hmonoid: "Group_Theory.monoid {0..m-1} (\<lambda> x y. ((x + y) mod m)) (0 :: int)"
    by (unfold_locales, auto simp add: of_nat_diff, presburger)
  moreover have "monoid.invertible {0..int (m - 1)} (\<lambda>x y. (x + y) mod int m) 0 u" if "u \<in> {0..int (m - 1)}" for u 
  proof(cases "u = 0")
    case True
    then show ?thesis using monoid.invertible_def[OF hmonoid that] monoid.unit_invertible[OF hmonoid] by simp
  next
    case hx: False
    then have "((m - u) + u) mod m = 0" and "(u + (m - u)) mod m = 0" and "m - u \<in> {0..int(m-1)}"
      using atLeastAtMost_iff hx that by auto 
    then show ?thesis using monoid.invertible_def[OF hmonoid that] by metis
  qed
  moreover have "commutative_monoid {0..m-1} (\<lambda> x y. ((x + y) mod m)) (0 :: int)"
    using hmonoid commutative_monoid_def commutative_monoid_axioms_def by (smt (verit))
  ultimately show ?thesis by (simp add: abelian_group_def group_def group_axioms_def 
      hmonoid)
next
  case hm: False
  moreover have hmonoid: "Group_Theory.monoid {0} (\<lambda> x y. ((x + y) mod m)) (0 :: int)"
    by (unfold_locales, auto)
  moreover have "monoid.invertible {0} (\<lambda>x y. (x + y) mod int m) 0 0" using monoid.invertible_def[OF hmonoid]
    monoid.unit_invertible[OF hmonoid] hm by simp
  ultimately show ?thesis by (unfold_locales, auto)
qed

lemma (in subgroup_of_group) prime_order_simple:
  assumes "prime (card G)"
  shows "H = {\<one>} \<or> H = G"
proof-
  have "card H dvd card G" using lagrange assms card.infinite dvdI not_prime_0 by fastforce
  then have "card H = 1 \<or> card H = card G" using assms prime_nat_iff by blast
  then show ?thesis using card_1_singletonE sub_unit_closed card.infinite card_subset_eq sub
    assms not_prime_0 subsetI insertE empty_iff by metis
qed

lemma residue_group_simple:
  assumes "prime p" and "subgroup H {0..(p :: nat)-1} (\<lambda> x y. ((x + y) mod p)) (0 :: int)"
  shows "H = {0} \<or> H = {0..int(p-1)}"
proof-
  have hprime: "prime (card {0..int(p-1)})" using card_atLeastAtMost_int assms int_ops by auto
  moreover have hsub:"subgroup_of_group H {0..(p :: nat)-1} (\<lambda> x y. ((x + y) mod p)) (0 :: int)" 
    using subgroup_of_group_def assms abelian_group_def residue_group by fast
  ultimately show ?thesis using assms subgroup_of_group.prime_order_simple[OF hsub hprime] by blast
qed

end
