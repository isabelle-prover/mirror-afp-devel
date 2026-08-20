theory Sumset_Basics
  imports Main
begin

definition sumset :: "('a::comm_monoid_add) set => 'a set => 'a set" where
  "sumset A B = {x. \<exists>a\<in>A. \<exists>b\<in>B. x = a + b}"

lemma sumset_iff:
  "x \<in> sumset A B \<longleftrightarrow> (\<exists>a\<in>A. \<exists>b\<in>B. x = a + b)"
  by (auto simp: sumset_def)

lemma sumsetI [intro]:
  assumes "a \<in> A" "b \<in> B"
  shows "a + b \<in> sumset A B"
  using assms by (auto simp: sumset_def)

lemma sumsetE [elim]:
  assumes "x \<in> sumset A B"
  obtains a b where "a \<in> A" "b \<in> B" "x = a + b"
  using assms by (auto simp: sumset_def)

lemma sumset_as_image:
  "sumset A B = case_prod (+) ` (A \<times> B)"
  by (auto simp: sumset_def)

lemma sumset_commute:
  "sumset A B = sumset B A"
  unfolding sumset_def using add.commute by blast

lemma empty_sumset_left [simp]:
  "sumset {} B = {}"
  by (auto simp: sumset_def)

lemma empty_sumset_right [simp]:
  "sumset A {} = {}"
  by (auto simp: sumset_def)

lemma sumset_assoc:
  fixes A B C :: "('a::comm_monoid_add) set"
  shows "sumset (sumset A B) C = sumset A (sumset B C)"
  unfolding sumset_def using add.assoc by force

lemma sumset_zero_right [simp]:
  fixes A :: "('a::comm_monoid_add) set"
  shows "sumset A {0} = A"
  by (auto simp: sumset_def)

lemma sumset_zero_left [simp]:
  fixes A :: "('a::comm_monoid_add) set"
  shows "sumset {0} A = A"
  by (auto simp: sumset_def)


definition translate :: "'a::comm_monoid_add => 'a set => 'a set" where
  "translate c A = ((+) c) ` A"

lemma translate_iff:
  "x \<in> translate c A \<longleftrightarrow> (\<exists>a\<in>A. x = c + a)"
  by (auto simp: translate_def)

lemma translate_empty [simp]:
  "translate c {} = {}"
  by (simp add: translate_def)

lemma translate_compose:
  "translate c (translate d A) = translate (c + d) A"
  by (simp add: translate_def image_image add_ac)

lemma translate_as_sumset:
  "translate c A = sumset {c} A"
  by (auto simp: translate_def sumset_def)

lemma finite_sumset [intro]:
  assumes "finite A" "finite B"
  shows "finite (sumset A B)"
  unfolding sumset_as_image
  using assms by (intro finite_imageI finite_cartesian_product)

lemma card_sumset_le:
  assumes "finite A" "finite B"
  shows "card (sumset A B) \<le> card A * card B"
proof -
  have "card (sumset A B) = card (case_prod (+) ` (A \<times> B))"
    by (simp add: sumset_as_image)
  also have "... \<le> card (A \<times> B)"
    using assms by (intro card_image_le finite_cartesian_product)
  also have "... = card A * card B"
    using assms by simp
  finally show ?thesis .
qed

lemma card_translate_eq:
  fixes A :: "('a::cancel_comm_monoid_add) set"
  assumes "finite A"
  shows "card (translate c A) = card A"
proof -	
  have "inj_on ((+) c) A"
    by (rule inj_onI) simp
  with assms show ?thesis
    by (simp add: translate_def card_image)
qed

lemma translate_Compl:
  fixes A :: "('a::ab_group_add) set"
  shows "translate c (UNIV - A) = UNIV - translate c A"
  by (simp add: translate_def translation_Compl flip: Compl_eq_Diff_UNIV)

lemma card_complement_translate_eq:
  fixes A :: "('a::{finite,ab_group_add}) set"
  shows "card (UNIV - translate c A) = card (UNIV - A)"
proof -
  have "card (translate c (UNIV - A)) = card (UNIV - A)"
    by (simp add: card_translate_eq)
  then show ?thesis
    using translate_Compl[of c A] by simp
qed

lemma sumset_pair_zero:
  fixes A :: "('a::comm_monoid_add) set"
  shows "sumset A {0, d} = A \<union> translate d A"
proof
  show "sumset A {0, d} \<subseteq> A \<union> translate d A"
  proof
    fix x
    assume "x \<in> sumset A {0, d}"
    then obtain a where a_in: "a \<in> A" and x_cases: "x = a \<or> x = a + d"
      by (auto simp: sumset_def)
    then consider "x = a" | "x = a + d"
      by blast
    then show "x \<in> A \<union> translate d A"
    proof cases
      case 1
      then show ?thesis
        using a_in by auto
    next
      case 2
      have "x = d + a"
        using 2 by (simp add: add.commute)
      then show ?thesis
        using a_in by (auto simp: translate_def)
    qed
  qed
next
  show "A \<union> translate d A \<subseteq> sumset A {0, d}"
  proof
    fix x
    assume "x \<in> A \<union> translate d A"
    then show "x \<in> sumset A {0, d}"
    proof
      assume "x \<in> A"
      then show ?thesis
      proof -
        have "0 \<in> {0, d}"
          by simp
        have "x + 0 \<in> sumset A {0, d}"
          using \<open>x \<in> A\<close> \<open>0 \<in> {0, d}\<close> by (rule sumsetI)
        then show ?thesis
          by simp
      qed
    next
      assume "x \<in> translate d A"
      then obtain a where a_in: "a \<in> A" and x_eq: "x = d + a"
        by (auto simp: translate_def)
      then show ?thesis
        by (auto intro!: sumsetI simp: add.commute)
    qed
  qed
qed

end

