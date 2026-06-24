theory Modular_Sumsets
  imports
    Sumset_Basics
    "HOL-Number_Theory.Number_Theory"
begin

section \<open>Modular sumsets over integer representatives of \<open>\<int>/p\<int>\<close>\<close>

text \<open>
  This theory provides a concrete, self-contained companion to the abstract
  prime-field development. It works with the canonical integer representatives
  \<open>0, \<dots>, p - 1\<close> of \<open>\<int>/p\<int>\<close> and records the basic cardinality behaviour of
  modular translations and singleton sumsets in that representation.
\<close>

definition residues :: "nat => int set" where
  "residues p = {0..<int p}"

definition mod_translate :: "nat => int => int set => int set" where
  "mod_translate p c A = ((\<lambda>x. (x + c) mod int p) ` A)"

definition mod_sumset :: "nat => int set => int set => int set" where
  "mod_sumset p A B = {x. \<exists>a\<in>A. \<exists>b\<in>B. x = (a + b) mod int p}"

lemma residues_finite [simp]:
  "finite (residues p)"
  by (simp add: residues_def)

lemma card_residues [simp]:
  assumes "0 < p"
  shows "card (residues p) = p"
  using assms by (simp add: residues_def)

lemma mod_translate_iff:
  "x \<in> mod_translate p c A \<longleftrightarrow> (\<exists>a\<in>A. x = (a + c) mod int p)"
  by (auto simp: mod_translate_def)

lemma mod_sumset_iff:
  "x \<in> mod_sumset p A B \<longleftrightarrow> (\<exists>a\<in>A. \<exists>b\<in>B. x = (a + b) mod int p)"
  by (auto simp: mod_sumset_def)

lemma mod_sumset_as_image:
  "mod_sumset p A B = ((\<lambda>x. x mod int p) ` sumset A B)"
  by (auto simp: mod_sumset_def sumset_def)

lemma mod_translate_subset_residues:
  assumes "0 < p"
  shows "mod_translate p c A \<subseteq> residues p"
  using assms by (auto simp: mod_translate_def residues_def)

lemma mod_sumset_subset_residues:
  assumes "0 < p"
  shows "mod_sumset p A B \<subseteq> residues p"
  using assms by (auto simp: mod_sumset_def residues_def)

lemma mod_sumset_singleton_left:
  "mod_sumset p {a} B = mod_translate p a B"
proof
  show "mod_sumset p {a} B \<subseteq> mod_translate p a B"
  proof
    fix x
    assume "x \<in> mod_sumset p {a} B"
    then obtain b where "b \<in> B" "x = (a + b) mod int p"
      by (auto simp: mod_sumset_def)
    then show "x \<in> mod_translate p a B"
      by (auto simp: mod_translate_def add.commute)
  qed
next
  show "mod_translate p a B \<subseteq> mod_sumset p {a} B"
  proof
    fix x
    assume "x \<in> mod_translate p a B"
    then obtain b where "b \<in> B" "x = (b + a) mod int p"
      by (auto simp: mod_translate_def)
    then show "x \<in> mod_sumset p {a} B"
      by (auto simp: mod_sumset_def add.commute)
  qed
qed

lemma mod_sumset_singleton_right:
  "mod_sumset p A {b} = mod_translate p b A"
  by (auto simp: mod_sumset_def mod_translate_def ac_simps)

lemma mod_translate_inj_on_residues:
  assumes "0 < p"
  shows "inj_on (\<lambda>x. (x + c) mod int p) (residues p)"
proof (rule inj_onI)
  fix x y
  assume x_in: "x \<in> residues p"
  assume y_in: "y \<in> residues p"
  assume eq: "(x + c) mod int p = (y + c) mod int p"

  have cong_xyc: "[x + c = y + c] (mod int p)"
    using eq by (simp add: cong_def)
  then have cong_xy: "[x = y] (mod int p)"
    by (simp add: cong_add_rcancel)

  from x_in have x_bounds: "0 \<le> x" "x < int p"
    by (auto simp: residues_def)
  from y_in have y_bounds: "0 \<le> y" "y < int p"
    by (auto simp: residues_def)

  show "x = y"
    by (rule cong_less_imp_eq_int[OF x_bounds y_bounds cong_xy])
qed

lemma card_mod_translate_eq:
  assumes "0 < p"
  assumes "A \<subseteq> residues p"
  shows "card (mod_translate p c A) = card A"
proof -
  have finite_A: "finite A"
    using assms by (meson finite_subset residues_finite)
  have inj_residues: "inj_on (\<lambda>x. (x + c) mod int p) (residues p)"
    by (rule mod_translate_inj_on_residues[OF assms(1)])
  have inj_A: "inj_on (\<lambda>x. (x + c) mod int p) A"
    by (rule inj_on_subset[OF inj_residues assms(2)])
  show ?thesis
    unfolding mod_translate_def
    by (simp add: card_image finite_A inj_A)
qed

lemma card_mod_sumset_singleton_left:
  assumes "0 < p"
  assumes "B \<subseteq> residues p"
  shows "card (mod_sumset p {a} B) = card B"
  using assms by (simp add: mod_sumset_singleton_left card_mod_translate_eq)

lemma card_mod_sumset_singleton_right:
  assumes "0 < p"
  assumes "A \<subseteq> residues p"
  shows "card (mod_sumset p A {b}) = card A"
  using assms by (simp add: mod_sumset_singleton_right card_mod_translate_eq)

text \<open>
  These lemmas complement the abstract prime-field proofs of Cauchy-Davenport
  and Vosper by providing a convenient API for expressing the corresponding
  cardinality facts over the standard residue representatives of prime cyclic
  groups.
\<close>

end

