(*
  File:   Harmonic_Numbers.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Definition and elementary facts about Harmonic numbers.
*)

section {* Harmonic numbers *}
theory Harmonic_Numbers
  imports
    Main
    Transcendental
begin

definition harm :: "nat \<Rightarrow> 'a :: real_normed_field" where
  "harm n = (\<Sum>k=1..n. inverse (of_nat k))"

lemma harm_altdef: "harm n = (\<Sum>k<n. inverse (of_nat (Suc k)))"
  unfolding harm_def by (induction n) simp_all

lemma harm_Suc: "harm (Suc n) = harm n + inverse (of_nat (Suc n))"
  by (simp add: harm_def)

lemma harm_nonneg [simp]: "harm n \<ge> (0 :: 'a :: {real_normed_field,linordered_field})"
  unfolding harm_def by (intro setsum_nonneg) simp_all

lemma harm_pos: "n > 0 \<Longrightarrow> harm n > (0 :: 'a :: {real_normed_field,linordered_field})"
  unfolding harm_def by (intro setsum_pos) simp_all
  
lemma of_real_harm: "of_real (harm n) = harm n"
  unfolding harm_def by simp
  
lemma norm_harm: "norm (harm n) = harm n"
  by (subst of_real_harm [symmetric]) (simp add: harm_nonneg)

lemma harm_expand: 
  "harm 0 = 0"
  "harm (Suc 0) = 1"
  "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)"
proof -
  have "numeral n = Suc (pred_numeral n)" by simp
  also have "harm \<dots> = harm (pred_numeral n) + inverse (numeral n)"
    by (subst harm_Suc, subst numeral_eq_Suc[symmetric]) simp
  finally show "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)" .
qed (simp_all add: harm_def)

lemma harm_pos_iff [simp]: "harm n > (0 :: 'a :: {real_normed_field,linordered_field}) \<longleftrightarrow> n > 0"
  by (rule iffI, cases n, simp add: harm_expand, simp, rule harm_pos)

lemma ln_diff_le_inverse:
  assumes "x \<ge> (1::real)"
  shows   "ln (x + 1) - ln x < 1 / x"
proof -
  from assms have "\<exists>z>x. z < x + 1 \<and> ln (x + 1) - ln x = (x + 1 - x) * inverse z"
    by (intro MVT2) (auto intro!: derivative_eq_intros simp: field_simps)
  then obtain z where z: "z > x" "z < x + 1" "ln (x + 1) - ln x = inverse z" by auto
  have "ln (x + 1) - ln x = inverse z" by fact
  also from z(1,2) assms have "\<dots> < 1 / x" by (simp add: field_simps)
  finally show ?thesis .
qed

lemma ln_le_harm: "ln (real n + 1) \<le> (harm n :: real)"
proof (induction n)
  fix n assume IH: "ln (real n + 1) \<le> harm n"
  have "ln (real (Suc n) + 1) = ln (real n + 1) + (ln (real n + 2) - ln (real n + 1))" by simp
  also have "(ln (real n + 2) - ln (real n + 1)) \<le> 1 / real (Suc n)"
    using ln_diff_le_inverse[of "real n + 1"] by (simp add: add_ac real_of_nat_def)
  also note IH
  also have "harm n + 1 / real (Suc n) = harm (Suc n)" by (simp add: harm_Suc field_simps)
  finally show "ln (real (Suc n) + 1) \<le> harm (Suc n)" by - (simp add: real_of_nat_def)
qed (simp_all add: harm_def)

end