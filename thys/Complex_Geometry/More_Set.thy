(* ---------------------------------------------------------------------------- *)
subsection \<open>Library Aditions for Set Cardinality\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>In this section some additional simple lemmas about set cardinality are proved.\<close>

theory More_Set
imports Main
begin

text \<open>Every infinite set has at least two different elements\<close>
lemma infinite_contains_2_elems:
  assumes "infinite A"
  shows "\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A"
  by (metis assms finite.simps is_singletonI' is_singleton_def)

text \<open>Every infinite set has at least three different elements\<close>
lemma infinite_contains_3_elems:
  assumes "infinite A"
  shows "\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A"
  by (metis Diff_iff assms infinite_contains_2_elems infinite_remove insertI1)

text \<open>Every set with cardinality greater than 1 has at least two different elements\<close>
lemma card_geq_2_iff_contains_2_elems:
  shows "card A \<ge> 2 \<longleftrightarrow> finite A \<and> (\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A)"
proof (intro iffI conjI)
  assume *: "finite A \<and> (\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A)"
  thus "card A \<ge> 2"
    by (metis card_0_eq card_Suc_eq empty_iff leI less_2_cases singletonD)
next
  assume *: "2 \<le> card A"
  then show "finite A"
    using card.infinite by force
  show "\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A"
    by (meson "*" card_2_iff' in_mono obtain_subset_with_card_n)
qed

text \<open>Set cardinality is at least 3 if and only if it contains three different elements\<close>
lemma card_geq_3_iff_contains_3_elems:
  shows "card A \<ge> 3 \<longleftrightarrow> finite A \<and> (\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A)"
proof (intro iffI conjI)
  assume *: "card A \<ge> 3"
  then show "finite A"
    using card.infinite by force
  show "\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A"
    by (smt (verit, best) "*" card_2_iff' card_geq_2_iff_contains_2_elems le_cases3 not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)
next
  assume *: "finite A \<and> (\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A)"
  thus "card A \<ge> 3"
    by (metis One_nat_def Suc_le_eq card_2_iff' card_le_Suc0_iff_eq leI numeral_3_eq_3 one_add_one order_class.order.eq_iff plus_1_eq_Suc)
qed

text \<open>Set cardinality of A is equal to 2 if and only if A={x, y} for two different elements x and y\<close>
lemma card_eq_2_iff_doubleton: "card A = 2 \<longleftrightarrow> (\<exists> x y. x \<noteq> y \<and> A = {x, y})"
  using card_geq_2_iff_contains_2_elems[of A]
  using card_geq_3_iff_contains_3_elems[of A]
  by auto (rule_tac x=x in exI, rule_tac x=y in exI, auto)

lemma card_eq_2_doubleton:
  assumes "card A = 2" and "x \<noteq> y" and "x \<in> A" and "y \<in> A"
  shows "A = {x, y}"
  using assms card_eq_2_iff_doubleton[of A]
  by auto

text \<open>Bijections map singleton to singleton sets\<close>

lemma bij_image_singleton:
  shows "\<lbrakk>f ` A = {b}; f a = b; bij f\<rbrakk> \<Longrightarrow> A = {a}"
  by (metis bij_betw_def image_empty image_insert inj_image_eq_iff)

end