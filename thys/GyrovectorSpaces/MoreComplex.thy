theory MoreComplex
imports Complex_Main "HOL-Analysis.Inner_Product"
begin

lemma real_compex_cmod:
  fixes r::real 
  shows "cmod(r * z) = abs r * cmod z"
  by (metis abs_mult norm_of_real)

lemma cnj_closed_for_unit_disc:
  assumes "cmod z1 < 1"
  shows "cmod (cnj z1) <1"
  by (simp add: assms)

lemma mult_closed_for_unit_disc:
  assumes "cmod z1 < 1" "cmod z2 < 1"
  shows "cmod (z1*z2) < 1"
  using assms(1) assms(2) norm_mult_less 
  by fastforce

lemma cnj_cmod:
  shows "z1 * cnj z1 = (cmod z1)^2"
  using complex_norm_square
  by fastforce

lemma cnj_cmod_1:
  assumes "cmod z1 = 1"
  shows "z1 * cnj z1 = 1"
  by (metis assms complex_cnj_one complex_norm_square mult.right_neutral norm_one)

lemma den_not_zero:
  assumes "cmod a < 1" "cmod b < 1"
  shows "1 + cnj a * b \<noteq> 0"
  using assms
  by (smt add.inverse_unique complex_mod_cnj i_squared norm_ii norm_mult norm_mult_less)

lemma cmod_mix_cnj:
  assumes "cmod u < 1" "cmod v < 1"
  shows "cmod ((1 + u*cnj v) / (1 + v*cnj u)) = 1"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) complex_cnj_add complex_cnj_cnj complex_cnj_mult complex_cnj_one complex_mod_cnj den_not_zero divide_self_if mult.commute norm_divide norm_one)

lemma cnj_mix_ex_real_k: 
  assumes "v \<noteq> 0"
  shows "x * cnj v = v * cnj x \<longleftrightarrow> (\<exists> (k::real). x = k * v)"
proof-
  have vx: "v = Re v + Im v * \<i>" "x = Re x + Im x * \<i>"
    by (simp add: complex_eq mult.commute)+

  have "x * cnj v = v * cnj x \<longleftrightarrow> (Re x + Im x * \<i>) * (Re v - Im v * \<i>) = (Re v + Im v * \<i>) * (Re x - Im x * \<i>)"
    by (metis complex_cnj_add complex_cnj_complex_of_real complex_cnj_i complex_cnj_mult complex_eq complex_of_real_i diff_conv_add_uminus i_complex_of_real mult_minus_left)   
  also have "\<dots> \<longleftrightarrow> (Re v * Im x - Re x * Im v) * \<i> =
                    (- Re v * Im x + Re x * Im v) * \<i>"
    by (simp add: field_simps)
  also have "\<dots> \<longleftrightarrow> Re v * Im x = Re x * Im v"
    by (smt (verit, best) complex_i_not_zero mult_minus_left mult_right_cancel of_real_eq_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists> (k::real). x = k * v)"
  proof (cases "Im v = 0")
    case True
    then show ?thesis
      using assms vx
      by (smt (verit, best) Im_divide_of_real add.right_neutral calculation complex_cnj_complex_of_real complex_cnj_mult complex_eq mult.commute mult_eq_0_iff nonzero_mult_div_cancel_left of_real_0 times_divide_eq_right)
  next
    case False
    then have "Re v * Im x = Re x * Im v \<longleftrightarrow> x = (Im x / Im v) * v"
      using assms vx
      by (smt (verit, ccfv_SIG) calculation complex_cnj_complex_of_real complex_cnj_mult complex_of_real_mult_Complex complex_surj mult.commute nonzero_mult_div_cancel_right times_divide_eq_left)
    then show ?thesis
      using assms vx
      by (smt (verit, del_insts) calculation complex_cnj_complex_of_real complex_cnj_mult mult.assoc mult.commute)
  qed
  finally show ?thesis
    .
qed

lemma two_inner_cnj:
  shows "2 * inner u v = cnj u * v + cnj v * u"
  by (smt (verit) cnj.simps(1) cnj.simps(2) cnj_add_mult_eq_Re inner_complex_def mult.commute mult_minus_left times_complex.simps(1))

abbreviation "cor \<equiv> complex_of_real"

lemma abs_inner_lt_1:
  assumes "norm u < 1" "norm v < 1"
  shows "abs (inner u v) < 1"
  using Cauchy_Schwarz_ineq2[of u v]
  by (smt (verit) assms(1) assms(2) mult_le_cancel_left2 norm_not_less_zero)

lemma inner_lt_1:
  assumes "norm u < 1" "norm v < 1"
  shows "inner u v < 1"
  using assms
  using abs_inner_lt_1
  by fastforce

lemma inner_def1: 
  shows "inner z1 z2 = (z1 * cnj z2 + z2 * cnj z1) / 2"
proof-
  obtain "a" "b" where ab: "Re z1 = a \<and> Im z1 = b"
    by blast
  obtain "c" "d" where cd: "Re z2 = c \<and> Im z2 = d"
    by blast
  have "Re (z1 * cnj z2) = a*c + b*d" "Re (z2 * cnj z1) = a*c + b*d"
       "Im (z1 * cnj z2) = b*c - a*d" "Im (z2 * cnj z1) = -b*c + a*d"
    using ab cd
    by simp+
  then have "(z1 * cnj z2 + z2 * cnj z1) / 2 =  a*c + b*d"
    using complex_eq_iff by force
  then show ?thesis
    using ab cd inner_complex_def
    by presburger
qed

lemma inner_def2:
  shows "inner z1 z2 = Re (cnj z1 * z2)"
  by (simp add: inner_complex_def)


end