section\<open>The Pl\"{u}nnecke-Ruzsa Inequality\<close>

text\<open>Authors: Angeliki Koutsoukou-Argyraki and Lawrence C. Paulson, University of Cambridge.\<close>

text\<open>We formalise Pl\"{u}nnecke's inequality and the Pl\"{u}nnecke-Ruzsa inequality, 
following the notes by Timothy Gowers: "Introduction to Additive
Combinatorics" (2022) for the University of Cambridge. To this end, we first introduce basic definitions
and prove elementary facts on sumsets and difference sets. Then, we show (two versions of)
the Ruzsa triangle inequality. We follow with a proof due to Petridis. \<close>

theory Pluennecke_Ruzsa_Inequality
  imports
    "Jacobson_Basic_Algebra.Ring_Theory"
    Complex_Main

begin

notation plus (infixl "+" 65)
notation minus (infixl "-" 65)
notation uminus ("- _" [81] 80)

subsection \<open>Key definitions (sumset, difference set) and basic lemmas \<close>

text \<open>Working in an arbitrary Abelian group, with additive syntax\<close>

locale additive_abelian_group = abelian_group G "(\<oplus>)" \<zero>
  for G and addition (infixl "\<oplus>" 65)  and zero ("\<zero>") 

begin

abbreviation G_minus:: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>" 70)
  where "x \<ominus> y \<equiv> x \<oplus> inverse y "

lemma inverse_closed: "x \<in> G \<Longrightarrow> inverse x \<in> G"
  by blast


subsubsection \<open>Sumsets\<close>

inductive_set sumset :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" for A B
  where
    sumsetI[intro]: "\<lbrakk>a \<in> A; a \<in> G; b \<in> B; b \<in> G\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> sumset A B"

lemma sumset_eq: "sumset A B = {c. \<exists>a \<in> A \<inter> G. \<exists>b \<in> B \<inter> G. c = a \<oplus> b}"
  by (auto simp: sumset.simps elim!: sumset.cases)

lemma sumset: "sumset A B = (\<Union>a \<in> A \<inter> G. \<Union>b \<in> B \<inter> G. {a \<oplus> b})"
  by (auto simp: sumset_eq)

lemma sumset_subset_carrier: "sumset A B \<subseteq> G"
  by (auto simp: sumset_eq)

lemma sumset_Int_carrier [simp]: "sumset A B \<inter> G = sumset A B"
  by (simp add: Int_absorb2 sumset_subset_carrier)

lemma sumset_mono: "\<lbrakk>A' \<subseteq> A; B' \<subseteq> B\<rbrakk> \<Longrightarrow> sumset A' B' \<subseteq> sumset A B"
  by (auto simp: sumset_eq)

lemma sumset_insert1: "NO_MATCH {} A \<Longrightarrow> sumset (insert x A) B = sumset {x} B \<union> sumset A B"
  by (auto simp: sumset_eq)

lemma sumset_insert2: "NO_MATCH {} B \<Longrightarrow> sumset A (insert x B) = sumset A {x} \<union> sumset A B"
  by (auto simp: sumset_eq)

lemma sumset_subset_Un1: "sumset (A \<union> A') B = sumset A B \<union> sumset A' B"
  by (auto simp: sumset_eq)

lemma sumset_subset_Un2: "sumset A (B \<union> B') = sumset A B \<union> sumset A B'"
  by (auto simp: sumset_eq)

lemma sumset_subset_insert: "sumset A B \<subseteq> sumset A (insert x B)" "sumset A B \<subseteq> sumset (insert x A) B"
  by (auto simp: sumset_eq)

lemma sumset_subset_Un: "sumset A B \<subseteq> sumset A (B\<union>C)" "sumset A B \<subseteq> sumset (A\<union>C) B"
  by (auto simp: sumset_eq)

lemma sumset_empty [simp]: "sumset A {} = {}" "sumset {} A = {}"
  by (auto simp: sumset_eq)

lemma sumset_empty':
  assumes "A \<inter> G = {}"
  shows "sumset B A = {}" "sumset A B = {}"
  using assms by (auto simp: sumset_eq)

lemma sumset_is_empty_iff [simp]: "sumset A B = {} \<longleftrightarrow> A \<inter> G = {} \<or> B \<inter> G = {}"
  by (auto simp: sumset_eq)

lemma sumset_D [simp]: "sumset A {\<zero>} = A \<inter> G" "sumset {\<zero>} A = A \<inter> G"
  by (auto simp: sumset_eq)

lemma sumset_Int_carrier_eq [simp]: "sumset A (B \<inter> G) = sumset A B" "sumset (A \<inter> G) B = sumset A B"
  by (auto simp: sumset_eq)

lemma sumset_assoc:
  shows "sumset (sumset A B) C = sumset A (sumset B C)"
  by (fastforce simp add: sumset_eq associative Bex_def)

lemma sumset_commute:
  shows "sumset A B = sumset B A"
  by (auto simp: sumset_eq; meson Int_iff commutative)

lemma finite_sumset:
  assumes "finite A" "finite B"  shows "finite (sumset A B)"
  using assms by (auto simp: sumset_eq)

lemma finite_sumset':
  assumes "finite (A \<inter> G)" "finite (B \<inter> G)"
    shows "finite (sumset A B)"
  using assms by (auto simp: sumset_eq)

lemma sumsetdiff_sing: "sumset (A - B) {x} = sumset A {x} - sumset B {x}"
  by (auto simp: sumset_eq)

lemma card_sumset_singleton_eq:
  assumes "finite A" shows "card (sumset A {a}) = (if a \<in> G then card (A \<inter> G) else 0)"
proof (cases "a \<in> G")
  case True
  then have "sumset A {a} = (\<lambda>x. x \<oplus> a) ` (A \<inter> G)"
    by (auto simp: sumset_eq)
  moreover have "inj_on (\<lambda>x. x \<oplus> a) (A \<inter> G)"
    by (auto simp: inj_on_def True)
  ultimately show ?thesis
    by (metis True card_image)
qed (auto simp: sumset_eq)

lemma card_sumset_le:
  assumes "finite A" shows "card (sumset A {a}) \<le> card A"
  by (simp add: assms card_mono card_sumset_singleton_eq)

lemma infinite_sumset_aux:
  assumes "infinite (A \<inter> G)"
  shows "infinite (sumset A B) \<longleftrightarrow> B \<inter> G \<noteq> {}"
proof (cases "B \<inter> G = {}")
  case False
  then obtain b where b: "b \<in> B" "b \<in> G" by blast
  with assms commutative have "((\<oplus>)b) ` (A \<inter> G) \<subseteq> sumset A B"
    by (auto simp: sumset)
  moreover have "inj_on ((\<oplus>)b) (A \<inter> G)"
    by (meson IntD2 b inj_onI invertible invertible_left_cancel)
  ultimately show ?thesis
    by (metis False assms inj_on_finite)
qed (auto simp: sumset_eq)

lemma infinite_sumset_iff:
  shows  "infinite (sumset A B) \<longleftrightarrow> infinite (A \<inter> G) \<and> B \<inter> G \<noteq> {} \<or> A \<inter> G \<noteq> {} \<and> infinite (B \<inter> G)"
  by (metis (no_types, lifting) finite_sumset' infinite_sumset_aux sumset_commute)

lemma card_le_sumset:
  assumes A: "finite A" "a \<in> A" "a \<in> G"
    and   B: "finite B" "B \<subseteq> G"
  shows "card B \<le> card (sumset A B)"
proof -
  have "B \<subseteq> (\<oplus>) (inverse a) ` sumset A B"
    using A B
    apply (clarsimp simp: sumset image_iff)
    by (metis Int_absorb2 Int_iff invertible invertible_left_inverse2)
  with A B show ?thesis
    by (meson  finite_sumset surj_card_le)
qed

lemma card_sumset_0_iff': "card (sumset A B) = 0 \<longleftrightarrow> card (A \<inter> G) = 0 \<or> card (B \<inter> G) = 0"
proof (cases "infinite (A \<inter> G) \<or> infinite (B \<inter> G)")
  case True
  then show ?thesis
    by (metis card_eq_0_iff infinite_sumset_iff sumset_empty')
qed (auto simp: sumset_eq)

lemma card_sumset_0_iff:
  assumes "A \<subseteq> G" "B \<subseteq> G"
  shows "card (sumset A B) = 0 \<longleftrightarrow> card A = 0 \<or> card B = 0"
  by (metis assms le_iff_inf card_sumset_0_iff')

lemma card_sumset_leq:
  assumes "A \<subseteq> G"
  shows "card(sumset A A) \<le> Suc(card A) choose 2"
  using assms
proof (induction "card A" arbitrary: A)
  case 0
  then show ?case
    by (metis card_sumset_0_iff zero_le)
next
  case (Suc n A)
  then obtain a A' where a: "a \<in> A" "A' = A - {a}" "a \<in> G"
    by (metis Zero_neq_Suc card_eq_0_iff subset_empty subset_eq)
  then have n: "card A' = n"
    by (metis Suc(2) card_Diff_singleton diff_Suc_Suc minus_nat.diff_0 One_nat_def)
  have "finite A"
    by (metis Suc(2) Zero_neq_Suc card.infinite)
  have "card (sumset A A) \<le> card (sumset A' A') + card A"
  proof -
    have A: "A = A' \<union> {a}"
      using a by auto
    then have "sumset A A = (sumset A' A') \<union> (sumset A {a})"
      by (auto simp: sumset_eq commutative)
    with a \<open>finite A\<close> card_sumset_le show ?thesis
      by (simp add: order_trans[OF card_Un_le])
  qed
  also have "\<dots> \<le> (card A) choose 2 + card A"
    using Suc a by (metis add_le_mono1 insert_Diff_single insert_absorb insert_subset n)
  also have "\<dots> \<le> Suc (card A) choose 2"
    by (simp add: numeral_2_eq_2)
  finally show ?case .
qed


subsubsection \<open>Iterated sumsets\<close>

definition sumset_iterated :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set"
  where "sumset_iterated A r \<equiv> Finite_Set.fold (sumset \<circ> (\<lambda>_. A)) {\<zero>} {..<r}"

lemma sumset_iterated_0 [simp]: "sumset_iterated A 0 = {\<zero>}"
  by (simp add: sumset_iterated_def)

lemma sumset_iterated_Suc [simp]: "sumset_iterated A (Suc k) = sumset A (sumset_iterated A k)"
  (is "?lhs = ?rhs")
proof -
  interpret comp_fun_commute_on "{..k}" "sumset \<circ> (\<lambda>_. A)"
    using sumset_assoc sumset_commute by (auto simp: comp_fun_commute_on_def)
  have "?lhs = (sumset \<circ> (\<lambda>_. A)) k (Finite_Set.fold (sumset \<circ> (\<lambda>_. A)) {\<zero>} {..<k})"
    unfolding sumset_iterated_def lessThan_Suc
    by (subst fold_insert, auto)
  also have "\<dots> = ?rhs"
    by (simp add: sumset_iterated_def)
  finally show ?thesis .
qed

lemma sumset_iterated_2:
  shows "sumset_iterated A 2 = sumset A A"
  by (simp add: eval_nat_numeral)

lemma sumset_iterated_r: "r > 0 \<Longrightarrow> sumset_iterated A r = sumset A (sumset_iterated A (r-1))"
  using gr0_conv_Suc by force

lemma sumset_iterated_subset_carrier: "sumset_iterated A k \<subseteq> G"
  by (cases k; simp add: sumset_subset_carrier)

lemma finite_sumset_iterated: "finite A \<Longrightarrow> finite (sumset_iterated A r)"
  by(induction r) (auto simp: finite_sumset)

lemma sumset_iterated_empty: "r>0 \<Longrightarrow> sumset_iterated {} r = {}"
  by (induction r) auto

subsubsection \<open>Difference sets\<close>

inductive_set minusset :: "'a set \<Rightarrow> 'a set" for A
  where
    minussetI[intro]: "\<lbrakk>a \<in> A; a \<in> G\<rbrakk> \<Longrightarrow> inverse a \<in> minusset A"

lemma minusset_eq: "minusset A = inverse ` (A \<inter> G)"
  by (auto simp: minusset.simps)


abbreviation "differenceset A B \<equiv> sumset A (minusset B)"

lemma minusset_is_empty_iff [simp]: "minusset A = {} \<longleftrightarrow> A \<inter> G = {}"
  by (auto simp: minusset_eq)

lemma minusset_triv [simp]: "minusset {\<zero>} = {\<zero>}"
  by (auto simp: minusset_eq)

lemma minusset_subset_carrier: "minusset A \<subseteq> G"
  by (auto simp: minusset_eq)

lemma minus_minusset [simp]: "minusset (minusset A) = A \<inter> G"
  apply (auto simp: minusset_eq)
  by (metis inverse_equality invertible invertibleE minusset.minussetI minusset_eq)

lemma card_minusset [simp]: "card (minusset A) = card (A \<inter> G)"
proof (rule bij_betw_same_card)
  show "bij_betw (inverse) (minusset A) (A \<inter> G)"
    unfolding minusset_eq by (force intro: bij_betwI)
qed

lemma card_minusset': "A \<subseteq> G \<Longrightarrow> card (minusset A) = card A"
  by (simp add: Int_absorb2)

lemma diff_minus_set:
  "differenceset (minusset A) B = minusset (sumset A B)" (is "?lhs = ?rhs")
proof (rule Set.set_eqI)
  fix u
  have "u \<in> ?lhs \<longleftrightarrow>
          (\<exists>x \<in> A \<inter> G. \<exists>y \<in> B \<inter> G. u = inverse x \<ominus> y)"
    by (auto simp: sumset minusset_eq)
  also have "\<dots> \<longleftrightarrow> (\<exists>x \<in> A \<inter> G. \<exists>y \<in> B \<inter> G. u = inverse (y \<oplus> x))"
    using inverse_composition_commute by auto
  also have "\<dots> \<longleftrightarrow> u \<in> ?rhs"
    by (auto simp: sumset minusset_eq commutative)
  finally show "u \<in> ?lhs \<longleftrightarrow> u \<in> ?rhs" .
qed

lemma differenceset_commute [simp]:
  shows "minusset (differenceset B A) = differenceset A B "
  by (metis diff_minus_set minus_minusset sumset_Int_carrier_eq(1) sumset_commute)

lemma card_differenceset_commute: "card (differenceset B A) = card (differenceset A B)"
    by (metis card_minusset' differenceset_commute sumset_subset_carrier)

lemma minusset_distrib_sum:
  shows "minusset (sumset A B) = sumset (minusset A) (minusset B)"
  by (simp add: diff_minus_set)

lemma minusset_iterated_minusset: "sumset_iterated (minusset A) k = minusset (sumset_iterated A k)"
  by (induction k) (auto simp: diff_minus_set)

lemma card_sumset_iterated_minusset:
  "card (sumset_iterated (minusset A) k) = card (sumset_iterated A k)"
  by (metis card_minusset' minusset_iterated_minusset sumset_iterated_subset_carrier)

lemma finite_minusset: "finite A \<Longrightarrow> finite (minusset A)"
  by (simp add: minusset_eq)

lemma finite_differenceset: "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (differenceset A B)"
  by (simp add: finite_minusset finite_sumset)


subsection\<open>The Ruzsa triangle inequality\<close>

lemma Ruzsa_triangle_ineq1:
  assumes U: "finite U" "U \<subseteq> G"
    and   V: "finite V" "V \<subseteq> G"
    and   W: "finite W" "W \<subseteq> G"
  shows "(card U) * card(differenceset V W) \<le> card (differenceset U V) * card (differenceset U W)"
proof -
  have fin:  "finite (differenceset U V)" "finite (differenceset U W)"
    using U V W finite_minusset finite_sumset by auto
  have "\<exists>v w. v \<in> V \<and> w \<in> W \<and> x = v \<ominus> w" if "x \<in> differenceset V W" for x
    using that by (auto simp: sumset_eq minusset_eq)
  then obtain v w where vinV: "v x \<in> V" and winW: "w x \<in> W" and vw_eq: "v x \<ominus> (w x) = x"
    if "x \<in> differenceset V W" for x    by metis
  have vinG: "v x \<in> G" and winG: "w x \<in> G" if "x \<in> differenceset V W" for x
    using V W that vinV winW by auto
  define \<phi> where "\<phi> \<equiv> \<lambda>(u,x). (u \<ominus> (v x), u \<ominus> (w x))"
  have "inj_on \<phi> (U \<times> differenceset V W)"
  proof (clarsimp simp add: \<phi>_def inj_on_def)
    fix u1 :: 'a and x1 :: 'a and u2 :: 'a and x2 :: 'a
    assume "u1 \<in> U" "u2 \<in> U"
      and x1: "x1 \<in> differenceset V W"
      and x2: "x2 \<in> differenceset V W"
      and v: "u1 \<ominus> v x1 = u2 \<ominus> v x2"
      and w: "u1 \<ominus> w x1 = u2 \<ominus> w x2"
    then obtain "u1 \<in> G" "u2 \<in> G" "x1 \<in> G" "x2 \<in> G"
      by (meson \<open>U \<subseteq> G\<close> subset_iff sumset_subset_carrier)
    show "u1 = u2 \<and> x1 = x2"
    proof
      have "v x1 \<ominus> w x1 = (u1 \<ominus> w x1) \<ominus> (u1 \<ominus> v x1)"
        by (smt (verit, del_insts) \<open>u1 \<in> G\<close> associative commutative composition_closed inverse_closed 
            invertible invertible_right_inverse2 vinG winG x1)
      also have "\<dots> = (u2 \<ominus> w x2) \<ominus> (u2 \<ominus> v x2)"
        using v w by presburger
      also have "\<dots> = v x2 \<ominus> w x2"
        by (smt (verit, del_insts) \<open>u2 \<in> G\<close> associative commutative composition_closed inverse_equality 
            invertible invertible_def invertible_right_inverse2 vinG winG x2)
      finally have "v x1 \<ominus> w x1 = v x2 \<ominus> w x2" .
      then show "x1=x2"
        by (simp add: x1 x2 vw_eq)
      then show "u1=u2"
        using \<open>u1 \<in> G\<close> \<open>u2 \<in> G\<close> w winG x1 by force
    qed
  qed
  moreover have "\<phi> \<in> (U \<times> differenceset V W) \<rightarrow> (differenceset U V) \<times> (differenceset U W)"
    using \<open>U \<subseteq> G\<close> \<open>V \<subseteq> G\<close> \<open>W \<subseteq> G\<close>
    by (fastforce simp: \<phi>_def intro: vinV winW)
  ultimately have "card (U \<times> differenceset V W) \<le> card (differenceset U V \<times> differenceset U W)"
    using card_inj fin by blast
  then show ?thesis
    by (simp flip: card_cartesian_product)
qed



definition Ruzsa_distance:: "'a set \<Rightarrow> 'a set \<Rightarrow> real"
    where "Ruzsa_distance A B \<equiv> card(differenceset A B)/(sqrt(card A) * sqrt(card B))"

lemma Ruzsa_triangle_ineq2:
  assumes U: "finite U" "U \<subseteq> G" "U \<noteq> {}"
    and   V: "finite V" "V \<subseteq> G"
    and   W: "finite W" "W \<subseteq> G"
  shows "Ruzsa_distance V W \<le> (Ruzsa_distance V U) * (Ruzsa_distance U W)"
proof -
  have  "card U * card (differenceset V W) \<le> card (differenceset U V) * card (differenceset U W)"
    using assms Ruzsa_triangle_ineq1 by metis
  \<comment>\<open>now divide both sides with the same quantity\<close>
  then have "card U * card (differenceset V W) / (card U * sqrt (card V) * sqrt (card W))
         \<le> card (differenceset U V) * card (differenceset U W) / (card U * sqrt (card V) * sqrt (card W))"
    using assms
    by (metis divide_right_mono mult_eq_0_iff mult_left_mono of_nat_0_le_iff of_nat_mono real_sqrt_ge_0_iff)
  then have *: "card(differenceset V W) / (sqrt(card V) * sqrt(card W)) \<le>
                card (differenceset U V) * card (differenceset U W)
                / (card U * sqrt(card V) * sqrt(card W))"
    using assms by simp
  have "card (differenceset U V) * card (differenceset U W)/(card U * sqrt(card V) * sqrt(card W))
                  = card(differenceset V U) / (sqrt(card U) * sqrt(card V))*
                    card(differenceset U W) / (sqrt(card U) * sqrt(card W))"
    using assms
    by (simp add: divide_simps) (metis card_minusset differenceset_commute minus_minusset)
  then have
     "card(differenceset V W) / (sqrt(card V) * sqrt(card W)) \<le>
       card(differenceset V U) / (sqrt(card U) * sqrt(card V)) *
       card(differenceset U W) / (sqrt(card U) * sqrt(card W))"
    using * assms by auto
  then show ?thesis unfolding Ruzsa_distance_def
    by (metis divide_divide_eq_left divide_divide_eq_left' times_divide_eq_right)
qed


subsection \<open>Petridis's proof of the Pl\"{u}nnecke-Ruzsa inequality \<close>

lemma Plu_2_2:
  assumes K0: "card (sumset A0 B) \<le> K0 * real (card A0)"
    and   A0: "finite A0" "A0 \<subseteq> G" "A0 \<noteq> {}"
    and   B: "finite B" "B \<subseteq> G" "B \<noteq> {}"
  obtains A K
    where "A \<subseteq> A0" "A \<noteq> {}" "0 < K" "K \<le> K0"
      and "\<And>C. C \<subseteq> G \<Longrightarrow> finite C \<Longrightarrow> card (sumset A (sumset B C)) \<le> K * real (card(sumset A C))"
proof
  define KS where "KS \<equiv> (\<lambda>A. card (sumset A B) / real (card A)) ` (Pow A0 - {{}})"
  define K where "K \<equiv> Min KS"
  define A where "A \<equiv> @A. A \<in> Pow A0 - {{}} \<and> K = card (sumset A B) / real (card A)"
  obtain KS: "finite KS" "KS \<noteq> {}"
    using KS_def A0 by blast
  then have "K \<in> KS"
    using K_def Min_in by blast
  then have "\<exists>A. A \<in> Pow A0 - {{}} \<and> K = card (sumset A B) / real (card A)"
    using KS_def by blast
  then obtain "A \<in> Pow A0 - {{}}" and Keq: "K = card (sumset A B) / real (card A)"
    by (metis (mono_tags, lifting) A_def someI_ex)
  then show A: "A \<subseteq> A0" "A \<noteq> {}"
    by auto
  with A0 finite_subset have "A \<subseteq> G" "finite A"
    by blast+
  have gt0: "0 < real (card (sumset A B)) / real (card A)" if "A \<noteq> {}" and "A \<subseteq> A0" for A
    using that assms
    by (smt (verit, best) order_trans card_0_eq card_sumset_0_iff divide_pos_pos of_nat_le_0_iff finite_subset)
  then show "K > 0"
    using A Keq by presburger
  have K_cardA: "K * (card A) = card (sumset A B)"
    unfolding Keq using Keq \<open>0 < K\<close> by force
  have K_le: "real (card (sumset A' B)) / card A' \<ge> K" if "A' \<subseteq> A" "A' \<noteq> {}" for A'
    using KS K_def KS_def \<open>A \<subseteq> A0\<close> that by force
  with A0 have "card (sumset A0 B) / real (card A0) \<in> KS"
    by (auto simp: KS_def)
  with A0 show "K \<le> K0"
    by (metis KS K_def Min_le_iff card_gt_0_iff mult_imp_div_pos_le of_nat_0_less_iff K0)
  show "card (sumset A (sumset B C)) \<le> K * real (card(sumset A C))"
    if "finite C" "C \<subseteq> G" for C
    using that
  proof (induction C)
    case empty
    then show ?case by simp
      \<comment> \<open>This is actually trivial: it does not follow from @{term "card (sumset A B) = K * card A"} 
         as claimed in the notes.\<close>
  next
    case (insert x C)
    then have "x \<in> G" "C \<subseteq> G" "finite C"
      by auto
    define A' where "A' \<equiv> A \<inter> {a. (a\<oplus>x) \<in> sumset A C}"
    with \<open>finite A\<close> have "finite A'" "A' \<subseteq> A" by auto
    then have [simp]: "real (card A - card A') = real (card A) - real (card A')"
      by (meson \<open>finite A\<close> card_mono of_nat_diff)
    have 0: "sumset A C \<inter> sumset (A - A') {x} = {}"
      by (clarsimp simp add: A'_def sumset_eq disjoint_iff) (metis IntI)
    have 1: "sumset A (insert x C) = sumset A C \<union> sumset (A - A') {x}"
      by (auto simp: A'_def sumset_eq)
    have "card (sumset A (insert x C)) = card (sumset A C) + card (sumset (A - A') {x})"
      by (simp add: 0 1 \<open>finite A\<close> card_Un_disjoint finite_sumset local.insert)
    also have "\<dots> = card (sumset A C) + card ((A - A') \<inter> G)"
      using \<open>finite A\<close> \<open>x \<in> G\<close> by (simp add: card_sumset_singleton_eq)
    also have "\<dots> = card (sumset A C) + card (A - A')"
      by (metis  \<open>A \<subseteq> G\<close> Int_absorb2 Int_Diff Int_commute)
    also have "\<dots> = card (sumset A C) + (card A - card A')"
      by (simp add: A'_def \<open>finite A\<close> card_Diff_subset)
    finally have *: "card (sumset A (insert x C)) = card (sumset A C) + (card A - card A')" .
    have "sumset A' (sumset B {x}) \<subseteq> sumset A (sumset B C)"
      by (clarsimp simp add: A'_def sumset_eq Bex_def) (metis associative commutative composition_closed) 
    then have "sumset A (sumset B (insert x C))
                 \<subseteq> sumset A (sumset B C) \<union> (sumset A (sumset B {x}) - sumset A' (sumset B {x}))"
      by (auto simp: sumset_insert2 sumset_subset_Un2)
    then have "card (sumset A (sumset B (insert x C))) \<le> card (sumset A (sumset B C))
                           + card ((sumset A (sumset B {x}) - sumset A' (sumset B {x})))"
      by (smt (verit, best) B(1) \<open>finite A\<close> \<open>finite C\<close> order_trans card_Un_le card_mono finite.emptyI
              finite.insertI finite_Diff finite_Un finite_sumset)
    also have "\<dots> = card (sumset A (sumset B C)) + (card (sumset A (sumset B {x})) - card (sumset A' (sumset B {x})))"
      by (simp add: \<open>A' \<subseteq> A\<close> \<open>finite A'\<close> \<open>finite B\<close> card_Diff_subset finite_sumset sumset_mono)
    also have "\<dots> \<le> card (sumset A (sumset B C)) + (card (sumset A B) - card (sumset A' B))"
      using \<open>finite A\<close> \<open>finite A'\<close> \<open>finite B\<close> by (simp add: card_sumset_singleton_eq finite_sumset flip: sumset_assoc)
    also have "\<dots> \<le> K * card (sumset A C) + (K * card A - K * card A')"
    proof (cases "A' =  {}")
      case True
      with local.insert \<open>C \<subseteq> G\<close> K_cardA show ?thesis by auto
    next
      case False
      then have "K * card A' \<le> real (card (sumset A' B))"
        using K_le[OF \<open>A' \<subseteq> A\<close>] by (simp add: divide_simps split: if_split_asm)
      then have "real (card (sumset A B) - card (sumset A' B)) \<le> K * real (card A) - K * real (card A')"
        by (simp add: B(1) K_cardA \<open>A' \<subseteq> A\<close> \<open>finite A\<close> card_mono finite_sumset of_nat_diff sumset_mono)
      with local.insert show ?thesis by simp
    qed
    also have "\<dots> \<le> K * real (card (sumset A (insert x C)))"
      using * \<open>A' \<subseteq> A\<close> by (simp add: algebra_simps)
    finally show ?case
      using of_nat_mono by blast
  qed
qed

lemma Cor_Plu_2_3:
  assumes K: "card (sumset A B) \<le> K * real (card A)"
    and   A: "finite A" "A \<subseteq> G" "A \<noteq> {}"
    and   B: "finite B" "B \<subseteq> G" 
  obtains A' where "A' \<subseteq> A" "A' \<noteq> {}"
                   "\<And>r. card (sumset A' (sumset_iterated B r)) \<le> K^r * real (card A')"
proof (cases "B = {}")
  case True
  have "K \<ge> 0"
    using assms by (simp add: True zero_le_mult_iff)
  moreover have *: "sumset_iterated B r = (if r=0 then {\<zero>} else {})" for r
    by (metis True sumset_iterated_0 sumset_iterated_empty zero_less_iff_neq_zero)
  ultimately have "real (card (sumset A (sumset_iterated B r)))
          \<le> K ^ r * real (card A)" for r
    by (simp add: "*" Int_commute  Int_absorb2 \<open>A \<subseteq> G\<close>)
  with \<open>A \<noteq> {}\<close> that show ?thesis by blast
next
  case False
  obtain A' K'
    where A': "A' \<subseteq> A" "A' \<noteq> {}" "0 < K'" "K' \<le> K"
      and A'_card: "\<And>C. C \<subseteq> G \<Longrightarrow> finite C \<Longrightarrow> card (sumset A' (sumset B C)) \<le> K' * real (card(sumset A' C))"
    by (metis A B Plu_2_2 K False)
  with A have "A' \<subseteq> G" by blast
  have *: "card (sumset A' (sumset_iterated B (Suc r))) \<le> K' * card (sumset A' (sumset_iterated B r))" 
          (is "?lhs \<le> ?rhs")
    for r
  proof -
    have "?lhs = card (sumset A' (sumset B (sumset_iterated B r)))"
      using that by (simp add: sumset_iterated_r)
    also have "\<dots> \<le> ?rhs"
      using A'_card B finite_sumset_iterated sumset_iterated_subset_carrier by meson
    finally show ?thesis .
  qed
  have **: "card (sumset A' (sumset_iterated B r)) \<le> K'^r * real (card A')" for r
  proof (induction r)
    case 0
    with \<open>A' \<subseteq> G\<close> show ?case
      by (simp add: Int_absorb2)
  next
    case (Suc r)
    then show ?case
      by (smt (verit) "*" \<open>0 < K'\<close> mult.commute mult.left_commute mult_le_cancel_left_pos power_Suc)
  qed
  show thesis
  proof
    show "real (card (sumset A' (sumset_iterated B r))) \<le> K ^ r * real (card A')" for r
      by (meson "**" A' order_trans less_eq_real_def mult_right_mono of_nat_0_le_iff power_mono)
  qed (use A' in auto)
qed


text\<open>The following Corollary of the above is an important special case,
also referred to as the original version of Pl\"{u}nnecke's inequality first shown by Pl\"{u}nnecke. \<close>

lemma Cor_Plu_2_3_Pluennecke_ineq:
  assumes K: "card (sumset A B) \<le> K * real (card A)"
    and   A: "finite A" "A \<subseteq> G" "A \<noteq> {}"
    and   B: "finite B" "B \<subseteq> G"
  shows "real (card (sumset_iterated B r)) \<le> K ^ r * real (card A)"
proof-
  obtain A' where *:"A' \<subseteq> A" "A' \<noteq> {}"
    "card (sumset A' (sumset_iterated B r)) \<le> K^r * real (card A')"
    using assms Cor_Plu_2_3 by metis
  with assms have  **: "card (sumset_iterated B r) \<le> card (sumset A' (sumset_iterated B r))"
    by (meson card_le_sumset finite_subset finite_sumset_iterated subset_empty subset_iff sumset_iterated_subset_carrier)
  with * show ?thesis
    by (smt (verit, best) A(1) K card_mono mult_left_mono of_nat_0_le_iff of_nat_le_iff zero_le_mult_iff zero_le_power)
qed

text \<open>Special case where @{term "B=A"}\<close>
lemma Cor_Plu_2_3_1:
  assumes K: "card (sumset A A) \<le> K * real (card A)"
    and   A: "finite A" "A \<subseteq> G" "A \<noteq> {}"
  shows "card (sumset_iterated A r) \<le> K^r * real (card A)"
proof -
  have "K > 0"
    by (meson A K Plu_2_2 less_le_trans)
  obtain A' where A': "A' \<subseteq> A" "A' \<noteq> {}"
    and A'_card: "\<And>r. card (sumset A' (sumset_iterated A r)) \<le> K^r * real (card A')"
    by (meson A Cor_Plu_2_3 K)
  with A obtain a where "a \<in> A'" "a \<in> G" "finite A'"
    by (metis ex_in_conv finite_subset subset_iff)
  then have "card (sumset_iterated A r) \<le> card (sumset A' (sumset_iterated A r))"
    using A card_le_sumset finite_sumset_iterated sumset_iterated_subset_carrier by meson
  also have "\<dots> \<le> K^r * real (card A')"
    using A'_card by meson
  also have "\<dots> \<le> K^r * real (card A)"
    by (simp add: \<open>A' \<subseteq> A\<close> \<open>finite A\<close> \<open>0 < K\<close> card_mono)
  finally show ?thesis
    by linarith
qed


text \<open>Special case where @{term "B=-A"}\<close>
lemma Cor_Plu_2_3_2:
  assumes K: "card (differenceset A A) \<le> K * real (card A)"
    and   A: "finite A" "A \<subseteq> G" "A \<noteq> {}"
  shows "card (sumset_iterated A r) \<le> K^r * real (card A)"
proof -
  have "card A > 0"
    by (simp add: A card_gt_0_iff)
  with K have "K \<ge> 0"
    by (smt (verit, del_insts) of_nat_0_less_iff of_nat_less_0_iff zero_le_mult_iff)
  obtain A' where A': "A' \<subseteq> A" "A' \<noteq> {}"
    and A'_card: "\<And>r. card (sumset A' (sumset_iterated (minusset A) r)) \<le> K^r * real (card A')"
    by (metis A Cor_Plu_2_3 assms(1) card_eq_0_iff card_minusset' minusset_subset_carrier)
  with A obtain a where "a \<in> A'" "a \<in> G" "finite A'"
    by (metis ex_in_conv finite_subset subset_iff)
  then have "card (sumset_iterated A r) \<le> card (sumset A' (sumset_iterated (minusset A) r))"
    by (metis A(1) card_le_sumset card_sumset_iterated_minusset finite_minusset finite_sumset_iterated sumset_iterated_subset_carrier)
  also have "\<dots> \<le> K^r * real (card A')"
    using A'_card by meson
  also have "\<dots> \<le> K^r * real (card A)"
    by (simp add: \<open>A' \<subseteq> A\<close> \<open>finite A\<close> \<open>0 \<le> K\<close> card_mono mult_left_mono)
  finally show ?thesis
    by linarith
qed

text \<open>The following result is known as the Pl\"{u}nnecke-Ruzsa inequality (Theorem 2.5
in Gowers's notes). The proof will make use of the Ruzsa triangle inequality.\<close>

theorem Pluennecke_Ruzsa_ineq:
  assumes K:  "card (sumset A B) \<le> K * real (card A)"
    and   A: "finite A" "A \<subseteq> G" "A \<noteq> {}"
    and   B: "finite B" "B \<subseteq> G" 
    and "0 < r" "0 < s"
  shows "card (differenceset (sumset_iterated B r) (sumset_iterated B s)) \<le> K^(r+s) * real(card A)"
proof -
  have "card A > 0"
    by (simp add: A card_gt_0_iff)
  with K have "K \<ge> 0"
    by (smt (verit, del_insts) of_nat_0_less_iff of_nat_less_0_iff zero_le_mult_iff)
  obtain A' where A': "A' \<subseteq> A" "A' \<noteq> {}"
    and A'_le: "\<And>r. card (sumset A' (sumset_iterated B r)) \<le> K^r * real (card A')"
    using  Cor_Plu_2_3 assms by metis
  define C where "C \<equiv> minusset A'"
  have "minusset C = A'" and "C \<noteq>{}" and cardA: "card A' \<le> card A" and cardC: "card C = card A'"
    using A' A card_mono by (auto simp: C_def card_minusset' Int_absorb2)
  then have cardCA: "card C \<le> card A" by linarith
  have "\<And>r. card (differenceset C (sumset_iterated B r)) \<le> K^r * real (card A')"
    using A'_le C_def card_minusset' diff_minus_set sumset_subset_carrier by presburger
  then have r: "card (differenceset C (sumset_iterated B r)) \<le> K^r * real (card C)"
    and  s: "card (differenceset C (sumset_iterated B s)) \<le> K^s * real (card C)"
    using cardC by presburger+
  have "card C > 0"
    by (metis A' \<open>finite A\<close> cardC card_gt_0_iff finite_subset)
  moreover have "C \<subseteq> G"
    by (simp add: C_def minusset_subset_carrier)
  ultimately have "card C * card (differenceset (sumset_iterated B r) (sumset_iterated B s))
        \<le> card (differenceset C (sumset_iterated B r)) *
           card (differenceset C (sumset_iterated B s))"
    by (meson Ruzsa_triangle_ineq1 B card_gt_0_iff finite_sumset_iterated sumset_iterated_subset_carrier)
  also have "\<dots> \<le> K^(r+s) * card C * card C"
    using mult_mono [OF r s] \<open>0 \<le> K\<close> by (simp add: power_add field_simps)
  finally have "card (differenceset (sumset_iterated B r) (sumset_iterated B s)) \<le> K^(r+s) * card C"
    using \<open>card C > 0\<close> by (simp add: field_simps)
  then show ?thesis
    by (smt (verit, ccfv_SIG) \<open>0 \<le> K\<close> cardA cardC mult_left_mono of_nat_mono zero_le_power)
qed

text \<open>The following is an alternative version of the Pl\"{u}nnecke-Ruzsa inequality (Theorem 2.1
in Gowers's notes).\<close>

theorem Pluennecke_Ruzsa_ineq_alt:
  assumes "finite A" "A \<subseteq> G"
    and "card (sumset A A) \<le> K * real (card A)" "r > 0" "s > 0"
  shows "card (differenceset (sumset_iterated A r) (sumset_iterated A s)) \<le> K^(r+s) * real(card A)"
proof (cases "A = {}")
  case True
  then have "sumset_iterated A r = {}" if "r>0" for r
    using sumset_iterated_empty that by force
  with assms show ?thesis
    by (auto simp: True)
next
  case False
  with assms Pluennecke_Ruzsa_ineq show ?thesis by presburger
qed

theorem Pluennecke_Ruzsa_ineq_alt_2:
  assumes "finite A" "A \<subseteq> G"
    and "card (differenceset A A) \<le> K * real (card A)" "r > 0" "s > 0"
  shows "card (differenceset (sumset_iterated A r) (sumset_iterated A s)) \<le> K^(r+s) * real(card A)"
proof (cases "A = {}")
  case True
  then have "sumset_iterated A r = {}" if "r>0" for r
    using sumset_iterated_empty that by force
  with assms show ?thesis
    by (auto simp: True)
next
  case False
  with assms Pluennecke_Ruzsa_ineq show ?thesis
    by (smt (verit, ccfv_threshold) card_minusset' differenceset_commute finite_minusset 
        minusset_distrib_sum minusset_iterated_minusset minusset_subset_carrier) 
qed

end


subsection \<open>Supplementary material on sumsets for sets of integers: basic inequalities\<close>

lemma moninv_int: "monoid.invertible UNIV (+) 0 u" for u::int
  using monoid.invertibleI [where v = "-u"] by (simp add: Group_Theory.monoid_def)

interpretation int: additive_abelian_group UNIV "(+)" "0::int"
  by unfold_locales (use moninv_int in auto)

lemma card_sumset_geq1:
  assumes A: "A \<noteq> {}" "finite A" and B: "B \<noteq> {}" "finite B"
  shows "card(int.sumset A B) \<ge> (card A) + (card B) - 1"
  using A
proof (induction "card A" arbitrary: A)
  case (Suc n)
  define a where "a = Max A"
  define A' where "A' \<equiv> A - {a}"
  then obtain a: "a \<in> A" "A' = A - {a}" "finite A'" "a \<notin> A'" and A: "A = insert a A'"
    using Max_in Suc a_def by blast
  with Suc have n: "card A' = n"
    by (metis card_Diff_singleton diff_Suc_Suc minus_nat.diff_0 One_nat_def)
  show ?case
  proof (cases "A' = {}")
    case True
    then show ?thesis
      by (simp add: A B(2) int.card_sumset_singleton_eq int.sumset_commute)
  next
    case False
    have "a + Max B \<notin> int.sumset A' B"
      using \<open>finite A\<close> \<open>finite B\<close>
      by (smt (verit, best) DiffE Max_ge a a_def int.sumset.cases singleton_iff)
    then have *: "\<not> int.sumset A' B \<union> (+) a ` B \<subseteq> int.sumset A' B"
      using B Max_in by blast
    have "card A + card B - 1 \<le> Suc (card (int.sumset A' B))"
      using Suc False A a using le_diff_conv by force
    also have "\<dots> \<le> card (int.sumset A' B \<union> (+) a ` B)"
      using a B
      by (metis "*" card_seteq finite_Un finite_imageI int.finite_sumset not_less_eq_eq sup_ge1)
    also have "\<dots> \<le> card (int.sumset A B)"
    proof (rule card_mono)
      show "finite (int.sumset A B)"
        using B Suc.prems int.finite_sumset by blast
      show "int.sumset A' B \<union> (+) a ` B \<subseteq> int.sumset A B"
        using A by (force simp: int.sumset)
    qed
    finally show ?thesis .
  qed
qed auto

lemma card_sumset_geq2:
  shows "card(int.sumset A A) \<ge> 2 * (card A) - 1"
  using card_sumset_geq1 [of A]
  by (metis mult.commute Nat.add_0_right card_eq_0_iff diff_0_eq_0 le0 mult_2_right)

end
