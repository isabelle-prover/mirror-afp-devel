theory PoincareDisc
  imports Complex_Main "HOL-Analysis.Inner_Product" GammaFactor
begin

typedef PoincareDisc = "{z::complex. cmod z < 1}"
  morphisms to_complex of_complex
  by (rule exI [where x=0], auto)

setup_lifting type_definition_PoincareDisc

lemma poincare_disc_two_elems:
  shows "\<exists> z1 z2::PoincareDisc. z1 \<noteq> z2"
proof-
  have "cmod 0 < 1"
    by simp
  moreover
  have "cmod (1/2) < 1"
    by simp
  moreover
  have "(0::complex) \<noteq> 1/2"
    by simp
  ultimately
  show ?thesis
    by transfer blast
qed

lift_definition inner_p :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" (infixl "\<cdot>" 100) is inner .

lift_definition norm_p :: "PoincareDisc \<Rightarrow> real"  ("\<llangle>_\<rrangle>" [100] 101) is norm .

lemma norm_lt_one:
  shows "\<llangle>u\<rrangle> < 1"
  by transfer simp

lemma norm_geq_zero:
  shows "\<llangle>u\<rrangle> \<ge> 0"
  by transfer simp

lemma square_norm_inner:
  shows "(\<llangle>u\<rrangle>)\<^sup>2 = u \<cdot> u"
  by transfer (simp add: dot_square_norm)

lift_definition gammma_factor_p :: "PoincareDisc \<Rightarrow> real" ("\<gamma>\<^sub>p") is gamma_factor .

lemma gamma_factor_p_nonzero [simp]:
  shows "\<gamma>\<^sub>p u \<noteq> 0"
  apply transfer
  unfolding gamma_factor_def
  using gamma_factor_nonzero
  by auto

lemma gamma_factor_p_positive [simp]:
  shows "\<gamma>\<^sub>p u > 0"
  by transfer (simp add: gamma_factor_positive)

lemma norm_square_gamma_factor_p:
  shows "(\<llangle>u\<rrangle>)^2 = 1 - 1 / (\<gamma>\<^sub>p u)^2"
  by transfer (simp add: norm_square_gamma_factor)

lemma norm_square_gamma_factor_p':
  shows "(\<llangle>u\<rrangle>)^2 = ((\<gamma>\<^sub>p u)^2 - 1) / (\<gamma>\<^sub>p u)^2"
  by transfer (simp add: norm_square_gamma_factor')

lemma gamma_factor_p_square_norm:
  shows "(\<gamma>\<^sub>p u)\<^sup>2 = 1 / (1 - (\<llangle>u\<rrangle>)\<^sup>2)"
  by transfer (simp add: gamma_factor_square_norm)

end
