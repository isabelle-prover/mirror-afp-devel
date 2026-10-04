theory Weierstrass_j_Invariant
  imports Weierstrass_Discriminant_Criterion
begin

section \<open>The partial j-invariant\<close>

definition weierstrass_j ::
    "'a::field weierstrass_coeffs \<Rightarrow> 'a option"
  where
  "weierstrass_j W =
    (if projective_weierstrass_nonsingular W
     then Some (c4 W ^ 3 / discriminant W)
     else None)"

lemma weierstrass_j_nonsingular:
  assumes "projective_weierstrass_nonsingular W"
  shows "weierstrass_j W = Some (c4 W ^ 3 / discriminant W)"
  using assms by (simp add: weierstrass_j_def)

lemma weierstrass_j_discriminant_nonzero:
  assumes "discriminant W \<noteq> 0"
  shows "weierstrass_j W = Some (c4 W ^ 3 / discriminant W)"
  using assms
  by (simp add: weierstrass_j_def weierstrass_nonsingular_iff)

lemma weierstrass_j_singular:
  assumes "\<not> projective_weierstrass_nonsingular W"
  shows "weierstrass_j W = None"
  using assms by (simp add: weierstrass_j_def)

lemma weierstrass_j_eq_none_iff [simp]:
  "weierstrass_j W = None \<longleftrightarrow> discriminant W = 0"
  unfolding weierstrass_j_def
  using weierstrass_nonsingular_iff[of W]
  by auto

lemma weierstrass_j_eq_some_iff:
  "weierstrass_j W = Some j \<longleftrightarrow>
    discriminant W \<noteq> 0 \<and> j = c4 W ^ 3 / discriminant W"
  unfolding weierstrass_j_def
  using weierstrass_nonsingular_iff[of W]
  by auto

lemma weierstrass_j_defined_iff:
  "weierstrass_j W \<noteq> None \<longleftrightarrow>
    projective_weierstrass_nonsingular W"
  unfolding weierstrass_j_def
  by auto

end
