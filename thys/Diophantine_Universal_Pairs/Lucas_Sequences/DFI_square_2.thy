theory DFI_square_2
  imports DFI_square_1 HOL.NthRoot
begin

lemma sun_lemma10_rec:
  fixes A::int and n::int and t::int and k::int
  assumes "A > 2" and "n > 3" and "\<chi>_int A n = 2*k"
  shows "(s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n))
      \<Longrightarrow> (\<psi>_int A s mod k = \<psi>_int A t mod k)"
proof -
  have rec1: "(s+t) mod (4*n) = (2*n) mod (4*n) \<Longrightarrow> \<psi>_int A s mod k = \<psi>_int A t mod k"
  proof -
    assume s_plus_t: "(s+t) mod (4*n) = (2*n) mod (4*n)"
    hence s_plus_t_2: "(s+t-2*n) mod (4*n) = 0 mod (4*n)"
      using mod_diff_cong[of "s+t" "4*n" "2*n" "2*n" "2*n"]  by auto
    hence s_plus_t_3: "(4*n) dvd (s+t-2*n)" by auto
    obtain q where q_def: "(s+t-2*n) = (4*n)*q" using s_plus_t_3
      by blast
    have "\<psi>_int A s mod k= \<psi>_int A (4*n*q + 2*n-t) mod k" using q_def by (smt (verit))
    hence "\<psi>_int A s mod k = \<psi>_int A (2*n-t) mod k"
      using technical_lemma2[of n A k q] assms by (smt (z3))
    hence "\<psi>_int A s mod k = (- \<psi>_int A (-t)) mod k"
      using assms technical_cor3[of n A k "-t"] by auto
    thus "\<psi>_int A s mod k = \<psi>_int A t mod k" using \<psi>_int_odd by auto
  qed
  have rec2: "s mod (4*n) = t mod (4*n) \<Longrightarrow> \<psi>_int A s mod k = \<psi>_int A t mod k"
  proof -
    assume s_eq_t: "s mod (4*n) = t mod (4*n)"
    obtain q where q_def: "s = 4*n*q + t" using s_eq_t by (smt (verit, ccfv_SIG) mod_eqE)
    thus "\<psi>_int A s mod k = \<psi>_int A t mod k" using q_def technical_lemma2[of n A k q] assms by auto
  qed
  show "(s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n))
      \<Longrightarrow> (\<psi>_int A s mod k = \<psi>_int A t mod k)"  using rec1 rec2 by blast
qed

text \<open>Some results about Lucas sequences seen as real numbers\<close>

lemma expr_of_\<psi>_and_\<chi>:
  fixes A::int and n::nat and \<alpha>::real
  assumes "A > 2" and "\<alpha>^2 = A^2-4" and "\<alpha> > 0"
  defines "\<beta>p \<equiv> (A+\<alpha>) / 2" and "\<beta>m \<equiv> (A-\<alpha>) / 2"
  shows "real_of_int (\<psi> A n) = (\<beta>p^n-\<beta>m^n) / \<alpha> \<and>
real_of_int (\<chi> A n) = \<beta>p^n+\<beta>m^n"
proof (induction n rule: \<psi>_induct)
  case 0
  then show ?case by auto
next
  case 1
  have "\<beta>p^1-\<beta>m^1 = \<beta>p - \<beta>m" by (auto simp add: algebra_simps)
  hence "\<beta>p^1-\<beta>m^1 = \<alpha>" using \<beta>p_def \<beta>m_def
    by (metis add.commute add_right_cancel diff_add_cancel real_average_minus_first)
  hence "(\<beta>p^1-\<beta>m^1) / \<alpha> = 1 \<and> real_of_int (\<psi> A 1) = 1" using assms by auto
  hence part_\<psi>: "real_of_int (\<psi> A 1) = (\<beta>p^1-\<beta>m^1) / \<alpha>" by metis
  have "\<beta>p^1+\<beta>m^1 = real_of_int A" unfolding \<beta>p_def \<beta>m_def
    by (smt (z3) field_sum_of_halves power_one_right)
  then show ?case using part_\<psi> by auto
next
  case (sucsuc n)
  note t = this
  have \<beta>p_eq: "A*\<beta>p-1 = \<beta>p^2"
  proof -
    have "\<beta>p^2 = (A+\<alpha>)*(A+\<alpha>)/4" unfolding \<beta>p_def using power2_eq_square[of "(A+\<alpha>) / 2"] by auto
    hence "\<beta>p^2 = (A^2+2*A*\<alpha>+\<alpha>^2)/4" by (auto simp add: power2_eq_square algebra_simps)
    hence "\<beta>p^2 = (A^2 + A*\<alpha> - 2)/2" using assms(2) by (auto simp add: algebra_simps)
    hence "\<beta>p^2 = A*(A+\<alpha>)/2 - 1" using power2_eq_square[of A]
      by (auto simp add: algebra_simps diff_divide_distrib)
    thus ?thesis using \<beta>p_def by auto
  qed
  have \<beta>m_eq: "A*\<beta>m-1 = \<beta>m^2"
  proof -
    have "\<beta>m^2 = (A-\<alpha>)*(A-\<alpha>)/4" unfolding \<beta>m_def using power2_eq_square[of "(A-\<alpha>) / 2"] by auto
    hence "\<beta>m^2 = (A^2-2*A*\<alpha>+\<alpha>^2)/4" by (auto simp add: power2_eq_square algebra_simps)
    hence "\<beta>m^2 = (A^2 - A*\<alpha> - 2)/2" using assms(2) by (auto simp add: algebra_simps)
    hence "\<beta>m^2 = (A*(A-\<alpha>) - 2)/2" by (auto simp add: algebra_simps power2_eq_square)
    hence "\<beta>m^2 = (A*(A-\<alpha>))/2 - 1" by (auto simp add: diff_divide_distrib)
    hence "\<beta>m^2 = A*(A-\<alpha>)/2 - 1" by auto
    thus ?thesis using \<beta>m_def by auto
  qed
  have "real_of_int (\<psi> A (Suc (Suc n))) =  A * (\<beta>p^(Suc n)-\<beta>m^(Suc n)) / \<alpha> - (\<beta>p^n-\<beta>m^n) / \<alpha>"
    using t by auto
  hence "real_of_int (\<psi> A (Suc (Suc n))) = (A * (\<beta>p*\<beta>p^n-\<beta>m*\<beta>m^n)) / \<alpha> - (\<beta>p^n-\<beta>m^n) / \<alpha>"
    by simp
  hence "real_of_int (\<psi> A (Suc (Suc n))) = (A * (\<beta>p*\<beta>p^n-\<beta>m*\<beta>m^n) - (\<beta>p^n-\<beta>m^n)) / \<alpha>"
    using assms by (smt (verit, ccfv_SIG) add_divide_distrib)
  hence "real_of_int (\<psi> A (Suc (Suc n))) = ((A*\<beta>p-1)*\<beta>p^n - (A*\<beta>m-1)*\<beta>m^n) / \<alpha>"
    by (auto simp add: algebra_simps)
  hence "real_of_int (\<psi> A (Suc (Suc n))) = (\<beta>p^2*\<beta>p^n - \<beta>m^2*\<beta>m^n)/\<alpha>" using \<beta>p_eq \<beta>m_eq by auto
  hence form_\<psi>: "real_of_int (\<psi> A (Suc (Suc n))) = (\<beta>p^(Suc (Suc n))-\<beta>m^(Suc (Suc n))) / \<alpha>"
    using power_add[of \<beta>p 2 n] power_add[of \<beta>m 2 n] by (metis add_2_eq_Suc)

  have "real_of_int (\<chi> A (Suc (Suc n))) =  A * (\<beta>p^(Suc n)+\<beta>m^(Suc n)) - (\<beta>p^n+\<beta>m^n)"
    using t by auto
  hence "real_of_int (\<chi> A (Suc (Suc n))) = (A * (\<beta>p*\<beta>p^n+\<beta>m*\<beta>m^n)) - (\<beta>p^n+\<beta>m^n)"
    by simp
  hence "real_of_int (\<chi> A (Suc (Suc n))) = (A*\<beta>p-1)*\<beta>p^n + (A*\<beta>m-1)*\<beta>m^n"
    by (auto simp add: algebra_simps)
  hence "real_of_int (\<chi> A (Suc (Suc n))) = \<beta>p^2*\<beta>p^n + \<beta>m^2*\<beta>m^n" using \<beta>p_eq \<beta>m_eq by auto
  hence form_\<chi>: "real_of_int (\<chi> A (Suc (Suc n))) = \<beta>p^(Suc (Suc n))+\<beta>m^(Suc (Suc n))"
    using power_add[of \<beta>p 2 n] power_add[of \<beta>m 2 n] by (metis add_2_eq_Suc)
  then show ?case using form_\<psi> form_\<chi> by auto
qed

lemma \<chi>_is_Bigger_sqrt5\<psi>: "A > 2 \<Longrightarrow> \<chi> A n > sqrt 5*\<psi> A n"
proof (cases n)
  case 0
  then show ?thesis by auto
next
  case (Suc k)
  note t = this
  assume A_def: "A > 2"
  hence "A \<ge> 3" by simp
  hence "A*A \<ge> 9" using mult_mono[of 3 A 3 A] A_def by auto
  hence DiscB4: "A^2-4 \<ge> 5" using power2_eq_square[of A] by auto
  define \<alpha> where "\<alpha> = sqrt(A^2-4)"
  have \<alpha>_def2: "\<alpha>^2 = A^2 - 4"
    unfolding \<alpha>_def using DiscB4 of_int_0_le_iff real_sqrt_pow2 by fastforce
  hence \<alpha>B2: "\<alpha> \<ge> sqrt 5"
    using DiscB4 apply simp by (metis DiscB4 \<alpha>_def of_int_le_iff of_int_numeral real_sqrt_le_iff)
  hence \<alpha>_pos: "\<alpha> > 0"
    by (meson not_numeral_le_zero order.trans real_sqrt_le_0_iff verit_comp_simplify1(3))
  define \<beta>p where "\<beta>p = (A+\<alpha>)/2"
  define \<beta>m where "\<beta>m = (A-\<alpha>)/2"
  have "\<alpha>^2 < A^2" using \<alpha>_def2 by auto
  hence "\<alpha> < A" using real_sqrt_less_iff[of "\<alpha>^2" "A^2"] A_def \<alpha>B2 by auto
  hence "\<beta>m > 0" using \<beta>m_def by simp
  hence \<beta>m_pos: "\<beta>m^n > 0" by auto
  have "\<chi> A n = \<beta>p^n+\<beta>m^n"
    unfolding \<beta>p_def \<beta>m_def using expr_of_\<psi>_and_\<chi>[of A \<alpha> n] \<alpha>_def2 A_def \<alpha>_pos by simp
  hence "\<chi> A n > \<beta>p^n - \<beta>m^n"
    using \<beta>m_pos diff_mono[of "\<beta>p^n+\<beta>m^n" "\<beta>p^n+\<beta>m^n" "2*\<beta>m^n" 0] by linarith
  hence "\<chi> A n > \<alpha> * ((\<beta>p^n - \<beta>m^n)/ \<alpha>)" using \<alpha>B2 by auto
  hence "\<chi> A n > \<alpha> * \<psi> A n"
    unfolding \<beta>p_def \<beta>m_def using expr_of_\<psi>_and_\<chi>[of A \<alpha> n] \<alpha>_def2 A_def \<alpha>_pos by simp
  hence "\<chi> A n > sqrt 5* \<psi> A n"
    using lucas_strict_monotonicity[of A k] t A_def \<alpha>B2 mult_left_mono[of "sqrt 5" \<alpha> "\<psi> A n"]
    by (smt (z3) mult_of_int_commute of_int_0_less_iff)
  then show ?thesis by auto
qed

lemma \<chi>_is_Bigger_2\<psi>: "A > 2 \<Longrightarrow> \<chi> A n > 2*\<psi> A n"
proof -
  assume A_def: "A > 2"
  have ineq: "sqrt 5 > 2"
    by (metis numeral_less_iff order_refl real_sqrt_four real_sqrt_less_iff semiring_norm(79))
  have "\<chi> A n > sqrt 5 * \<psi> A n" using \<chi>_is_Bigger_sqrt5\<psi> A_def by auto
  thus ?thesis using ineq mult_right_mono[of 2 "sqrt 5" "\<psi> A n"] A_def
    using lucas_monotone2[of A "0" n] by auto
qed

lemma \<psi>_ineq_opti:
  fixes A::int and n::nat
  assumes "A > 2"
  shows "5* \<psi> A n < 2*\<psi> A (n+1)"
proof -
  have "A \<ge> 3" using assms by simp
  hence "A*A \<ge> 9" using mult_mono[of 3 A 3 A] assms by auto
  hence DiscB4: "A^2-4 > 4" using power2_eq_square[of A] by auto
  define \<alpha> where "\<alpha> = sqrt(A^2-4)"
  have \<alpha>_def2: "\<alpha>^2 = A^2 - 4"
    unfolding \<alpha>_def using DiscB4 using of_int_0_le_iff real_sqrt_pow2 by fastforce
  hence \<alpha>B2: "\<alpha> > 2"
    using DiscB4 by (metis \<alpha>_def of_int_less_iff of_int_numeral real_sqrt_four real_sqrt_less_iff)
  define \<beta>p where "\<beta>p = (A+\<alpha>)/2"
  define \<beta>m where "\<beta>m = (A-\<alpha>)/2"
  have "\<alpha>^2 < A^2" using \<alpha>_def2 by auto
  hence "\<alpha> < A" using real_sqrt_less_iff[of "\<alpha>^2" "A^2"] assms \<alpha>B2 by auto
  hence "\<beta>m > 0" using \<beta>m_def by simp
  hence \<beta>m_pos: "\<beta>m^n > 0" by auto
  have \<beta>pB2: "\<beta>p > 5/2" unfolding \<beta>p_def using assms \<alpha>B2 by auto
  have "\<psi> A (n+1) = (\<beta>p^(n+1) - \<beta>m^(n+1))/ \<alpha>"
    using expr_of_\<psi>_and_\<chi>[of A \<alpha> "n+1"] assms \<alpha>_def2 \<alpha>B2 \<beta>p_def \<beta>m_def by fastforce
  hence "\<psi> A (n+1) = ((\<beta>p*\<beta>p^n - \<beta>p*\<beta>m^n) + (\<beta>p*\<beta>m^n - \<beta>m*\<beta>m^n))/ \<alpha>"
    using power_Suc[of \<beta>p n] power_Suc[of \<beta>m n] by simp
  hence "\<psi> A (n+1) = (\<beta>p*\<beta>p^n - \<beta>p*\<beta>m^n)/ \<alpha> + (\<beta>p*\<beta>m^n - \<beta>m*\<beta>m^n)/ \<alpha>"
    using add_divide_distrib[of "(\<beta>p*\<beta>p^n - \<beta>p*\<beta>m^n)" "(\<beta>p*\<beta>m^n - \<beta>m*\<beta>m^n)" \<alpha>] assms by simp
  hence "\<psi> A (n+1) = \<beta>p*(\<beta>p^n-\<beta>m^n)/ \<alpha> + \<beta>m^n*(\<beta>p-\<beta>m)/ \<alpha>" by (auto simp add: algebra_simps)
  hence "\<psi> A (n+1) = \<beta>p*\<psi> A n + \<beta>m^n*(\<beta>p-\<beta>m)/ \<alpha>"
    using \<beta>p_def \<beta>m_def expr_of_\<psi>_and_\<chi>[of A \<alpha> n] \<alpha>_def2 \<alpha>B2 assms by fastforce
  hence "\<psi> A (n+1) = \<beta>p*\<psi> A n + \<beta>m^n"
    using \<beta>p_def \<beta>m_def diff_divide_distrib[of "A+\<alpha>" "A-\<alpha>" 2] \<alpha>B2 apply simp by (simp add: \<beta>m_def)
  hence "\<psi> A (n+1) > \<beta>p * \<psi> A n" using \<beta>m_pos by auto
  thus ?thesis using \<beta>pB2 using lucas_monotone2[of A "0" n] assms mult_right_mono[of "5/2" \<beta>p "\<psi> A n"] by auto
qed

lemma \<psi>_doubles:
  fixes A::int and n::nat
  assumes "A > 2"
  shows "2*\<psi> A n < \<psi> A (n+1)"
proof -
  have "A \<ge> 3" using assms by simp
  hence "A*A \<ge> 9" using mult_mono[of 3 A 3 A] assms by auto
  hence DiscB4: "A^2-4 > 4" using power2_eq_square[of A] by auto
  define \<alpha> where "\<alpha> = sqrt(A^2-4)"
  have \<alpha>_def2: "\<alpha>^2 = A^2 - 4"
    unfolding \<alpha>_def using DiscB4 using of_int_0_le_iff real_sqrt_pow2 by fastforce
  hence \<alpha>B2: "\<alpha> > 2"
    using DiscB4 by (metis \<alpha>_def of_int_less_iff of_int_numeral real_sqrt_four real_sqrt_less_iff)
  define \<beta>p where "\<beta>p = (A+\<alpha>)/2"
  define \<beta>m where "\<beta>m = (A-\<alpha>)/2"
  have "\<alpha>^2 < A^2" using \<alpha>_def2 by auto
  hence "\<alpha> < A" using real_sqrt_less_iff[of "\<alpha>^2" "A^2"] assms \<alpha>B2 by auto
  hence "\<beta>m > 0" using \<beta>m_def by simp
  hence \<beta>m_pos: "\<beta>m^n > 0" by auto
  have \<beta>pB2: "\<beta>p > 2" unfolding \<beta>p_def using assms \<alpha>B2 by auto
  have "\<psi> A (n+1) = (\<beta>p^(n+1) - \<beta>m^(n+1))/ \<alpha>"
    using expr_of_\<psi>_and_\<chi>[of A \<alpha> "n+1"] assms \<alpha>_def2 \<alpha>B2 \<beta>p_def \<beta>m_def by fastforce
  hence "\<psi> A (n+1) = ((\<beta>p*\<beta>p^n - \<beta>p*\<beta>m^n) + (\<beta>p*\<beta>m^n - \<beta>m*\<beta>m^n))/ \<alpha>"
    using power_Suc[of \<beta>p n] power_Suc[of \<beta>m n] by simp
  hence "\<psi> A (n+1) = (\<beta>p*\<beta>p^n - \<beta>p*\<beta>m^n)/ \<alpha> + (\<beta>p*\<beta>m^n - \<beta>m*\<beta>m^n)/ \<alpha>"
    using add_divide_distrib[of "(\<beta>p*\<beta>p^n - \<beta>p*\<beta>m^n)" "(\<beta>p*\<beta>m^n - \<beta>m*\<beta>m^n)" \<alpha>] assms by simp
  hence "\<psi> A (n+1) = \<beta>p*(\<beta>p^n-\<beta>m^n)/ \<alpha> + \<beta>m^n*(\<beta>p-\<beta>m)/ \<alpha>" by (auto simp add: algebra_simps)
  hence "\<psi> A (n+1) = \<beta>p*\<psi> A n + \<beta>m^n*(\<beta>p-\<beta>m)/ \<alpha>"
    using \<beta>p_def \<beta>m_def expr_of_\<psi>_and_\<chi>[of A \<alpha> n] \<alpha>_def2 \<alpha>B2 assms by fastforce
  hence "\<psi> A (n+1) = \<beta>p*\<psi> A n + \<beta>m^n"
    using \<beta>p_def \<beta>m_def diff_divide_distrib[of "A+\<alpha>" "A-\<alpha>" 2] \<alpha>B2 apply simp by (simp add: \<beta>m_def)
  hence "\<psi> A (n+1) > \<beta>p * \<psi> A n" using \<beta>m_pos by auto
  thus ?thesis using \<beta>pB2 lucas_monotone2[of A "0" n] assms mult_right_mono[of 2 \<beta>p "\<psi> A n"] by auto
qed

lemma distinct_residus:
  fixes A::int and n::int and k::int and i::int and j::int
  assumes "A > 2" and "n > 3" and "\<chi>_int A n = 2*k" and "i\<in>{-n..n}" and "j\<in>{-n..n}" and "i\<noteq>j"
  shows "\<psi>_int A i mod k \<noteq> \<psi>_int A j mod k"
proof -
  have \<chi>_maj: "\<chi> A m > 2 * \<psi> A m" for m::nat
    using assms \<chi>_is_Bigger_2\<psi>[of A m] by simp

  have non_null: "l\<in>{1..n} \<longrightarrow> \<psi>_int A l mod k \<noteq> 0 \<and> \<psi>_int A (-l) mod k \<noteq> 0" for l
  proof
    assume lLen: "l\<in>{1..n}"
    hence notz: "\<psi> A (nat l) > 0" using assms lucas_strict_monotonicity[of "A" "nat l-1"] by force
    hence nonzero: "\<psi>_int A l > 0 \<and> \<psi>_int A (-l) < 0" unfolding \<psi>_int_def using lLen by force
    have "\<psi> A (nat l) \<le> \<psi> A (nat n)"
      using assms lLen lucas_monotone2[of A "nat l" "nat n - nat l"] by force
    hence "\<psi> A (nat l) < k"
      using \<chi>_maj[of "nat n"] assms unfolding \<chi>_int_def by auto
    hence "\<psi> A (nat l) mod k \<noteq> 0" using notz by simp
    thus "\<psi>_int A l mod k \<noteq> 0 \<and> \<psi>_int A (-l) mod k \<noteq> 0"
      unfolding \<psi>_int_def using lLen zmod_zminus1_not_zero by simp
  qed

  have prepart2:"l\<in>{1..n} \<and> m\<in>{1..n} \<and> l<m \<Longrightarrow> \<psi>_int A l mod k \<noteq> \<psi>_int A m mod k" for l m
  proof -
    assume assm: "l\<in>{1..n} \<and> m\<in>{1..n} \<and> l<m"
    then have "\<psi> A (nat l) < \<psi> A (nat m)"
      using \<psi>_int_def assms lucas_monotone2[of A "nat l" "nat m - nat l - 1"]
        lucas_strict_monotonicity[of A "nat m -1"] by force
    then have Le: "\<psi>_int A l < \<psi>_int A m" using assm \<psi>_int_def by simp
    have \<psi>lBe0: "\<psi>_int A l \<ge> 0"
      using assms \<psi>_int_def assm lucas_strict_monotonicity[of A "nat l - 1"] by simp
    have "\<psi> A (nat m) \<le> \<psi> A (nat n)"
      using lucas_monotone2[of A "nat m" "nat n - nat m"] assms assm by force
    then have "\<psi> A (nat m) < k"
      using \<open>n>3\<close> \<open>\<chi>_int A n = 2*k\<close> \<chi>_maj[of "nat n"] \<chi>_int_def[of A n] by simp
    then have "\<psi>_int A m < k" using \<psi>_int_def assm by simp
    then have "0 < \<psi>_int A m - \<psi>_int A l \<and> \<psi>_int A m - \<psi>_int A l < k" using Le \<psi>lBe0 by auto
    then have "(\<psi>_int A m - \<psi>_int A l) mod k \<noteq> 0" by simp
    then show "\<psi>_int A l mod k \<noteq> \<psi>_int A m mod k" by (metis dvd_imp_mod_0 mod_eq_dvd_iff)
  qed
  then have part2: "l\<noteq>m \<Longrightarrow> l\<in>{1..n} \<and> m\<in>{1..n} \<Longrightarrow> \<psi>_int A l mod k \<noteq> \<psi>_int A m mod k" for l m
  proof (cases "l<m")
    case True
    then show "l\<in>{1..n} \<and> m\<in>{1..n} \<Longrightarrow> \<psi>_int A l mod k \<noteq> \<psi>_int A m mod k"
      using prepart2[of l m] by simp
  next
    case False
    note t=this
    then show "l\<noteq>m \<Longrightarrow> l\<in>{1..n} \<and> m\<in>{1..n} \<Longrightarrow> \<psi>_int A l mod k \<noteq> \<psi>_int A m mod k"
    proof -
      assume "l\<noteq>m"
      then have "m<l" using t by simp
      then show "l\<in>{1..n} \<and> m\<in>{1..n} \<Longrightarrow> \<psi>_int A l mod k \<noteq> \<psi>_int A m mod k" using prepart2[of m l]
        by simp
    qed
  qed

  have small_result: "0 < a \<and> a < 2*k \<and> a \<noteq> k \<Longrightarrow> \<not> k dvd a" for a
  proof (rule ccontr)
    assume assm: "0 < a \<and> a < 2*k \<and> a \<noteq> k"
    have k_pos: "k > 0" using \<chi>_maj[of "nat n"] assms \<chi>_int_def[of A n] lucas_strict_monotonicity[of A "nat n-1"]
      by auto
    assume hypoth: "\<not> \<not> k dvd a"
    then obtain x where x_def: "k*x = a" by force
    consider (neg) "x \<le> 0" | (1) "x=1" | (pos) "x \<ge> 2" by linarith
    then show "False"
    proof (cases)
      case neg
      then show ?thesis using assm by (smt (verit, del_insts) x_def zero_less_mult_pos)
    next
      case 1
      then show ?thesis using assm x_def by simp
    next
      case pos
    then show ?thesis using assm k_pos mult_left_mono[of 2 x k] x_def by auto
    qed
  qed

  have rel_\<psi>_\<chi>_lin:"2*\<psi> A x = A*\<psi> A (x+1) - \<chi> A (x+1)" for x
  proof (induction x rule: \<psi>_induct)
    case 0
    then show ?case by auto
  next
    case 1
    then show ?case by auto
  next
    case (sucsuc n)
    note t = this
    have "A*\<psi> A (n+2+1) - \<chi> A (n+2+1) = A*(A*\<psi> A (n+1+1) - \<psi> A (n+1)) - (A*\<chi> A (n+1+1) - \<chi> A (n+1))"
      by auto
    hence "A*\<psi> A (n+2+1) - \<chi> A (n+2+1) = A*(A*\<psi> A (n+1+1) - \<chi> A (n+1+1)) - (A*\<psi> A (n+1) - \<chi> A (n+1))"
      by (auto simp add: algebra_simps)
    then show ?case using t by auto
  qed

  have prepart3: "l\<in>{1..n-1} \<Longrightarrow> (\<psi>_int A l + \<psi>_int A n) mod k \<noteq> 0 mod k" for l
  proof -
    have \<psi>_frac: "\<psi> A m \<le> \<psi> A (m+1) * 2/5" for m using assms \<psi>_ineq_opti[of A m] by auto
    assume assm: "l\<in>{1..n-1}"
    have \<psi>_pos: "0 < \<psi>_int A l \<and> 0 < \<psi>_int A n \<and> 0 < \<psi> A (nat n)"
      using assms assm \<psi>_int_def[of A l] \<psi>_int_def[of A n] lucas_strict_monotonicity[of A "nat l-1"]
        lucas_strict_monotonicity[of A "nat n-1"] by auto
    have lesser_2k: "\<psi>_int A l + \<psi>_int A n < 2*k"
      using \<psi>_int_def[of A l] \<psi>_int_def[of A n] assm assms lucas_monotone4[of A "nat l" "nat n"]
        \<chi>_maj[of "nat n"] \<chi>_int_def[of A n] apply simp by linarith
    have pos: "\<psi>_int A l + \<psi>_int A n > 0" using \<psi>_pos by auto
    consider (small) "l \<le> n-3" | (n_m2) "l = n-2" | (n_m1) "l = n-1" using assm by force
    then show ?thesis
    proof cases
      case small
      hence ineq1: "\<psi>_int A l + \<psi>_int A n \<le> \<psi> A (nat n - 3) + \<psi> A (nat n)"
        using assm \<psi>_int_def[of A l] \<psi>_int_def[of A n] lucas_monotone4[of A "nat l" "nat n-3"] assms
        by auto
      have nat_eq: "Suc (nat n-3) = nat n-2 \<and> Suc (nat n-2) = nat n-1 \<and> Suc (nat n-1) = nat n"
        using assms by auto
      hence "\<psi> A (nat n-3) \<le> \<psi> A (nat n) * 8/125"
        using assms \<psi>_frac[of "nat n-3"] \<psi>_frac[of "nat n - 2"] \<psi>_frac[of "nat n - 1"] by auto
      hence ineq2: "\<psi>_int A l + \<psi>_int A n \<le> \<psi> A (nat n)*(133/125)" using ineq1 by auto
      have ineq3: "133/125 < sqrt (5) / 2"
      proof -
        have obv: "125*sqrt 5 > 0 \<and> (266::int) > 0" by simp
        have obv2: "(133/125 < sqrt (5) / 2) = (266 < 125*sqrt 5)" by auto
        have "266^2 < (125*sqrt 5)^2" by auto
        hence "266 < 125*sqrt 5" using obv by (smt (z3) pos2 power_mono_iff)
        then show ?thesis using obv2 by auto
      qed
      hence "\<psi> A (nat n)*(133/125) < \<psi> A (nat n)*(sqrt 5 / 2)"
        using \<psi>_pos mult_strict_left_mono[of "\<psi> A (nat n)" "133/125" "sqrt 5 / 2"] by auto
      hence "\<psi>_int A l + \<psi>_int A n < (\<psi> A (nat n) * sqrt 5) / 2" using ineq2 by auto
      hence "\<psi>_int A l + \<psi>_int A n < k"
        using assms \<chi>_int_def[of A n] \<chi>_is_Bigger_sqrt5\<psi>[of A "nat n"]
        by (simp add: mult_of_int_commute)
      then show ?thesis using small_result[of "\<psi>_int A l + \<psi>_int A n"] pos lesser_2k by auto
    next
      case n_m2
      have "\<psi>_int A (n-2) + \<psi>_int A n \<noteq> k"
      proof (rule ccontr)
        have dev_nat: "nat (n - 2) = nat n - 2 \<and> nat n = Suc (Suc (nat n - 2))" using assms by auto
        assume hypoth: "\<not>(\<psi>_int A (n-2) + \<psi>_int A n \<noteq> k)"
        hence "2*(\<psi> A (nat (n - 2)) + \<psi> A (nat n)) = \<chi> A (nat n)"
          using assms \<psi>_int_def[of A "n-2"] \<psi>_int_def[of A n] \<chi>_int_def[of A n] by auto
        hence "2*(\<psi> A (nat n - 2) + \<psi> A (Suc (Suc (nat n - 2)))) = \<chi> A (nat n)"
          using dev_nat by simp
        hence "A*(2*\<psi> A (Suc (nat n - 2))) = \<chi> A (nat n)" by auto
        hence "A*(A*\<psi> A (Suc (nat n - 2) + 1) - \<chi> A (Suc (nat n - 2) + 1)) = \<chi> A (nat n)"
          using rel_\<psi>_\<chi>_lin[of "Suc (nat n - 2)"] by auto
        hence "A*(A*\<psi> A (nat n) - \<chi> A (nat n)) = \<chi> A (nat n)"
          using assms by (metis Suc_eq_plus1 dev_nat)
        hence "A^2*\<psi> A (nat n) = (A+1) * \<chi> A (nat n)"
          using power2_eq_square[of A] by (auto simp add: algebra_simps)
        hence "(A^2*\<psi> A (nat n))^2 = (A+1)^2*((A^2-4)*\<psi> A (nat n)^2 + 4)"
          using power_mult_distrib[of "A+1" "\<chi> A (nat n)" 2] lucas_pell_part3[of A "nat n"] by auto
        hence "((A+1)^2*(A^2-4)-A^2*A^2)*\<psi> A (nat n)^2 + 4*(A+1)^2 = 0"
          by (auto simp add: algebra_simps)
        hence "((A^2+2*A+1)*(A^2-4)-A^2*A^2) *\<psi> A (nat n)^2 + 4*(A+1)^2 = 0"
          using power2_sum[of A 1] apply simp by (smt (verit, best))
        hence "(2*A*A*A-3*A*A-8*A-4)*\<psi> A (nat n)^2 + 4*(A+1)^2 = 0"
          using power2_eq_square[of A] by (auto simp add: algebra_simps)
        hence equation: "((2*A+1)*(A+1)*(A-3)-1)*\<psi> A (nat n)^2 + 4*(A+1)^2 = 0"
          by (auto simp add: algebra_simps)
        have "4*(A+1)^2 \<ge> 64"
          using assms power2_eq_square[of "A+1"] mult_mono[of 4 "A+1" 4 "A+1"] by auto
        hence "((2*A+1)*(A+1)*(A-3)-1)*\<psi> A (nat n)^2 \<le> -64" using equation by auto
        hence "((2*A+1)*(A+1)*(A-3)-1) < 0"
          by (smt (verit, ccfv_SIG) \<psi>_pos assms(1) int_distrib(2) pos_zmult_eq_1_iff zero_less_power zmult_zless_mono2)
        hence ineq2: "(2*A+1)*(A+1)*(A-3) \<le> 0" by auto
        have "(2*A+1)*(A+1) > 0" using assms by auto
        hence "A=3" using ineq2 assms by (smt (verit) mult_pos_pos)
        hence "8^2 = \<psi> 3 (nat n)^2 " using equation by auto
        hence eq: "8 = \<psi> 3 (nat n)" using lucas_strict_monotonicity[of 3 "nat n-1"] assms apply simp
          by (smt (verit, ccfv_SIG) \<open>8\<^sup>2 = (\<psi> 3 (nat n))\<^sup>2\<close> power2_eq_imp_eq)
        have "\<psi> 3 3 = \<psi> 3 (Suc (Suc (Suc 0)))" using numeral_3_eq_3 by presburger
        hence eq2: "\<psi> 3 3 = \<psi> 3 (nat n)" using eq by auto
        hence "\<psi> 3 (Suc 3) > \<psi> 3 (nat n) \<and> nat n \<ge> Suc 3" using lucas_strict_monotonicity[of 3 3] assms by auto
        then show "False" using lucas_monotone4[of 3 "Suc 3" "nat n"] assms by auto
      qed
      hence "\<psi>_int A l + \<psi>_int A n \<noteq> k" using n_m2 by auto
     then show ?thesis using pos lesser_2k small_result[of "\<psi>_int A l + \<psi>_int A n"] by auto
    next
      case n_m1
      have "\<psi>_int A (n-1) + \<psi>_int A n \<noteq> k"
      proof (rule ccontr)
        have dev_nat: "nat (n-1) = nat n - 1 \<and> nat n - 1 +1 = nat n" using assms by auto
        assume hypoth: "\<not>(\<psi>_int A (n-1) + \<psi>_int A n \<noteq> k)"
        hence "2*\<psi> A (nat n - 1) + 2*\<psi> A (nat n) = \<chi> A (nat n)"
          using assms \<psi>_int_def[of A "n-1"] \<psi>_int_def[of A n] \<chi>_int_def[of A n] dev_nat by auto
        hence "A*\<psi> A (nat n) - \<chi> A (nat n) + 2*\<psi> A (nat n) = \<chi> A (nat n)"
          using rel_\<psi>_\<chi>_lin[of "nat n - 1"] dev_nat by auto
        hence "(A+2)*\<psi> A (nat n) = 2*\<chi> A (nat n)" by (auto simp add: algebra_simps)
        hence "(A+2)^2*\<psi> A (nat n)^2 = 4*((A^2-4)*\<psi> A (nat n)^2 +4)"
          using lucas_pell_part3[of A "nat n"] power_mult_distrib[of "A+2" "\<psi> A (nat n)" 2]
          by (auto simp add: algebra_simps)
        hence "(4*(A^2-4) - (A+2)^2)*\<psi> A (nat n)^2 + 16 = 0" by (auto simp add: algebra_simps)
        hence "(3*A*A-20 - 4*A)*\<psi> A (nat n)^2 +16 = 0"
          using power2_eq_square[of A] power2_sum[of A 2] by (auto simp add: algebra_simps)
        hence equation: "(3*A-10)*(A+2)*\<psi> A (nat n)^2 + 16 = 0" by (auto simp add: algebra_simps)
        have "(A+2)*\<psi> A (nat n)^2 > 0" using \<psi>_pos assms by auto
        hence "3*A-10 < 0"
          using equation by (smt (verit, ccfv_SIG) int_distrib(4) zmult_zless_mono2)
        hence "A=3" using assms by auto
        hence "5*\<psi> 3 (nat n)^2 = 16" using equation by auto
        hence "0 mod 5 = (16::int) mod 5" by presburger
      then show "False" by simp
    qed
    hence "\<psi>_int A l + \<psi>_int A n \<noteq> k" using n_m1 by auto
     then show ?thesis using pos lesser_2k small_result[of "\<psi>_int A l + \<psi>_int A n"] by auto
   qed
 qed

  have part3: "l\<in>{1..n} \<and> m\<in>{-n..-1} \<Longrightarrow> \<psi>_int A l mod k \<noteq> \<psi>_int A m mod k" for l m
  proof -
    assume assm: "l\<in>{1..n} \<and> m\<in>{-n..-1}"
    define h where "h = -m"
    consider (lesser_n) "l<n \<and> h<n" | (less_eq) "l<n \<and> h=n" | (eq_less) "l=n \<and> h<n"
            | (eq_n) "l=n \<and> h=n"
      using assm h_def apply simp by linarith
    thus ?thesis
    proof cases
      case lesser_n
      have lh_pos: "l > 0 \<and> h > 0" using assm h_def by auto
      have "\<psi>_int A l - \<psi>_int A m = \<psi>_int A l + \<psi>_int A h" using \<psi>_int_odd h_def by simp
      hence eq1: "\<psi>_int A l - \<psi>_int A m = \<psi> A (nat l) + \<psi> A (nat h)" using lh_pos \<psi>_int_def by auto
      hence diff_pos: "\<psi>_int A l - \<psi>_int A m > 0"
        using assms lucas_strict_monotonicity[of A "nat l - 1"] lucas_strict_monotonicity[of A "nat h - 1"] lh_pos by auto
      have "nat l \<le> nat n - 1 \<and> nat h \<le> nat n - 1" using lesser_n h_def by auto 
      have obv: "nat n - 1 + 1 = nat n \<and> nat n - 1 > 2" using assms by auto
      have "\<psi> A (nat l) + \<psi> A (nat h) \<le>2*\<psi> A (nat n-1)"
        using lesser_n lucas_monotone4[of A "nat l" "nat n-1"] lucas_monotone4[of A "nat h" "nat n-1"]
          assms by linarith
      hence "\<psi>_int A l - \<psi>_int A m < \<psi> A (nat n)" using eq1 \<psi>_doubles[of A "nat n-1"] assms obv
        by auto
      hence "\<psi>_int A l - \<psi>_int A m < k" using \<chi>_maj[of "nat n"] \<chi>_int_def[of A n] assms
        by simp
      hence "(\<psi>_int A l - \<psi>_int A m) mod k \<noteq> 0 mod k" using diff_pos by auto
      then show ?thesis using mod_diff_cong by fastforce
    next
      case less_eq
      hence "(\<psi>_int A h + \<psi>_int A l) mod k \<noteq> 0 mod k"
        using prepart3[of l] assm by (simp add: add.commute)
      hence "(\<psi>_int A l - \<psi>_int A m) mod k \<noteq> 0 mod k" using h_def \<psi>_int_odd by auto 
      then show ?thesis using mod_diff_cong by fastforce
    next
      case eq_less
      hence "(\<psi>_int A h + \<psi>_int A l) mod k \<noteq> 0 mod k"
        using prepart3[of h] assm h_def by (simp add: add.commute)
      hence "(\<psi>_int A l - \<psi>_int A m) mod k \<noteq> 0 mod k" using h_def \<psi>_int_odd by auto
      then show ?thesis using mod_diff_cong by fastforce
    next
      case eq_n
      have \<psi>B2: "\<psi> A (nat n) > 2" using lucas_monotone3[of A "nat n"] assms by auto
      have fund: "(20-A^2)*(\<psi> A (nat n))^2 \<noteq> 4"
      proof (cases "20-A^2 = 0")
        case True
        then show ?thesis by simp
      next
        case False
        have "abs ((20 - A^2)*(\<psi> A (nat n))^2) = abs (20 - A^2) * (\<psi> A (nat n) * \<psi> A (nat n))"
          using abs_mult[of "20-A^2" "\<psi> A (nat n)^2"] \<psi>B2 power2_eq_square[of "\<psi> A (nat n)"]
            abs_mult[of "\<psi> A (nat n)" "\<psi> A (nat n)"] by auto
        hence "abs ((20 - A^2)*(\<psi> A (nat n))^2) \<ge> \<psi> A (nat n) * \<psi> A (nat n)" 
          using False mult_right_mono[of 1 "abs (20 - A^2)" "\<psi> A (nat n) * \<psi> A (nat n)"] by auto
        hence "abs ((20 - A^2)*(\<psi> A (nat n))^2) > 4"
          using \<psi>B2 mult_strict_mono[of 2 "\<psi> A (nat n)" 2 "\<psi> A (nat n)"]
          by (auto simp add: mult_strict_mono)
        then show ?thesis by auto
      qed
      have "(20-A^2)*(\<psi> A (nat n))^2 = 4^2*(\<psi> A (nat n))^2 - (A^2-4)*(\<psi> A (nat n))^2"
        by (auto simp add: algebra_simps)
      hence "(20-A^2)*(\<psi> A (nat n))^2 = (4*(\<psi> A (nat n)))^2 - \<chi> A (nat n)^2 + 4"
        using lucas_pell_part3[of A "nat n"] by (auto simp add: algebra_simps)
      hence "(4*(\<psi> A (nat n)))^2 - \<chi> A (nat n)^2 \<noteq> 0" using fund by auto
      hence "4*\<psi> A (nat n) \<noteq> \<chi> A (nat n)" by algebra
      hence not_k: "\<psi>_int A l + \<psi>_int A h \<noteq> k" using assms eq_n \<psi>_int_def[of A n]
        using \<chi>_int_def add_cancel_right_right left_minus_one_mult_self
          mult.commute mult.left_commute power_add by fastforce
      have pos: "\<psi>_int A l + \<psi>_int A h > 0" using eq_n \<psi>_int_def[of A n] \<psi>B2 by auto
      have lesser_\<chi>: "\<psi>_int A l + \<psi>_int A h < 2*k"
        using assms eq_n \<chi>_maj[of "nat n"] \<psi>_int_def[of A n] \<chi>_int_def[of A n] by auto
      have not_dvd: "\<not> (k dvd (\<psi>_int A l + \<psi>_int A h))"
        using small_result[of "\<psi>_int A l + \<psi>_int A h"] pos not_k lesser_\<chi> by auto
      hence "(\<psi>_int A l - \<psi>_int A m) mod k \<noteq> 0 mod k" using \<psi>_int_odd[of A m] h_def by auto
      then show ?thesis using mod_diff_cong by fastforce
    qed
  qed

  consider (null_pos) "i=0 \<and> j>0" | (null_neg) "i=0 \<and> j<0" |
          (pos_null) "i>0 \<and> j=0" | (pos_pos) "i>0 \<and> j>0 \<and> i\<noteq>j" | (pos_neg) "i>0 \<and> j<0" |
          (neg_null) "i<0 \<and> j=0" | (neg_pos) "i<0 \<and> j>0" | (neg_neg) "i<0 \<and> j<0 \<and> i\<noteq>j"
    using \<open>j \<in> {- n..n}\<close> \<open>i \<in> {- n..n}\<close> by (metis assms(6) linorder_neqE_linordered_idom)
  then show ?thesis 
  proof cases
    case null_pos
    then show ?thesis using  \<psi>_int_def non_null[of j] \<open>j \<in> {- n..n}\<close> by force
    next
      case null_neg
      then show ?thesis using \<psi>_int_def non_null[of "-j"] \<open>j \<in> {- n..n}\<close> by force
    next
      case pos_null
      then show ?thesis using \<psi>_int_def non_null[of "i"] \<open>i \<in> {- n..n}\<close> by force
    next
      case pos_pos
      then show ?thesis using \<psi>_int_def part2[of "i" "j"] \<open>i \<in> {- n..n}\<close> \<open>j \<in> {- n..n}\<close> by force
    next
      case pos_neg
      then show ?thesis using part3[of i j] assms by auto
    next
      case neg_null
      then show ?thesis using \<psi>_int_def non_null[of "-i"] \<open>i \<in> {- n..n}\<close> by force
    next
      case neg_pos
      then show ?thesis using part3[of j i] assms by auto
    next
      case neg_neg
      then show ?thesis using \<psi>_int_def part2[of "-i" "-j"] \<open>i \<in> {- n..n}\<close> \<open>j \<in> {- n..n}\<close>
        apply simp by (metis equation_minus_iff mod_minus_cong)
  qed
qed


lemma case_lesser_than_4n:
  fixes A::int and n::int and s::int  and t::int and k::int
  assumes "A > 2" and "n > 3" and "\<chi>_int A n = 2*k" and "0\<le>s \<and> s<4*n \<and> 0\<le>t \<and> t<4*n"
  shows "(\<psi>_int A s mod k = \<psi>_int A t mod k)
      \<Longrightarrow> (s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n))"
proof -
  assume \<psi>_eq: "\<psi>_int A s mod k = \<psi>_int A t mod k"
  consider (11) "0\<le> s \<and> s\<le>n \<and> 0\<le>t   \<and> t\<le>n  " | (21) "n\<le>s \<and> s\<le>3*n \<and> 0\<le>t   \<and> t\<le>n  " | (41) "3*n\<le>s \<and> s\<le>4*n \<and> 0\<le>t   \<and> t\<le>n  " |
           (12) "0\<le> s \<and> s\<le>n \<and> n\<le>t   \<and> t\<le>3*n" | (22) "n\<le>s \<and> s\<le>3*n \<and> n\<le>t   \<and> t\<le>3*n" | (42) "3*n\<le>s \<and> s\<le>4*n \<and> n\<le>t \<and> t\<le>3*n" |
           (14) "0\<le> s \<and> s\<le>n \<and> 3*n\<le>t \<and> t\<le>4*n" | (24) "n\<le>s \<and> s\<le>3*n \<and> 3*n\<le>t \<and> t\<le>4*n" | (44) "3*n\<le>s \<and> s\<le>4*n \<and> 3*n\<le>t \<and> t\<le>4*n"
    using assms by (smt (verit) "11")
  thus ?thesis
  proof (cases)
    case 11
    have "s=t" using distinct_residus[of A n k s t] assms \<psi>_eq "11" by auto
then show ?thesis by simp
next
  case 21
  have ineq: "-n \<le> 2*n-s \<and> 2*n-s \<le> n" using "21" by auto
  have "\<psi>_int A (2*n-s) mod k = \<psi>_int A t mod k"
    using assms \<psi>_eq technical_lemma2[of n A k "-s"] \<psi>_int_odd[of A "-s"]
    by (smt (z3) sun_lemma10_rec)
  hence "t = 2*n-s" using distinct_residus[of A n k "2*n-s" t] "21" ineq assms by auto
  then show ?thesis by simp
next
  case 41
  have ineq: "-n \<le> -4*n+s \<and> -4*n+s \<le>n" using "41" by auto
  have "\<psi>_int A (-4*n+s) mod k = \<psi>_int A t mod k"
    using technical_lemma2_part2[of n A k "-1" s] \<psi>_eq assms by auto
  hence "t = -4*n+s" using distinct_residus[of A n k "-4*n+s" t] "41" ineq assms by auto
  then show ?thesis by simp
next
  case 12
  have ineq: "-n \<le> 2*n-t \<and> 2*n-t \<le> n" using "12" by auto
  have "\<psi>_int A (2*n-t) mod k = \<psi>_int A s mod k"
    using assms \<psi>_eq technical_lemma2[of n A k "-t"] \<psi>_int_odd[of A "-t"]
    by (smt (z3) sun_lemma10_rec)
  hence "s = 2*n-t" using distinct_residus[of A n k "2*n-t" s] "12" ineq assms by auto
  then show ?thesis by simp
next
  case 22
  have ineq: "-n \<le> 2*n-s \<and> 2*n-s \<le> n \<and> -n \<le> 2*n-t \<and> 2*n-t \<le> n" using "22" by auto
  have "\<psi>_int A (2*n-s) mod k = \<psi>_int A (2*n-t) mod k"
    using assms \<psi>_eq technical_lemma2[of n A k "-t"] technical_lemma2[of n A k "-s"]
      \<psi>_int_odd[of A "-s"] \<psi>_int_odd[of A "-s"] by (smt (z3) sun_lemma10_rec)
  hence "2*n-s = 2*n-t" using distinct_residus[of A n k "2*n-t" "2*n-s"] ineq assms by auto
  then show ?thesis by simp
next
  case 42
  have ineq: "-n \<le> s-4*n \<and> s-4*n \<le> n \<and> -n \<le> 2*n-t \<and> 2*n-t \<le> n" using "42" by auto
  have "\<psi>_int A (s-4*n) mod k = \<psi>_int A (2*n-t) mod k"
    using assms \<psi>_eq technical_lemma2[of n A k "-t"] technical_lemma2_part2[of n A k "-1" s]
      \<psi>_int_odd[of A "-t"] by (smt (z3) sun_lemma10_rec)
  hence "s-4*n = 2*n - t" using distinct_residus[of A n k "s-4*n" "2*n-t"] ineq assms by auto
  then show ?thesis by simp
next
  case 14
  have ineq: "-n \<le> -4*n+t \<and> -4*n+t \<le>n" using "14" by auto
  have "\<psi>_int A (-4*n+t) mod k = \<psi>_int A s mod k"
    using technical_lemma2_part2[of n A k "-1" t] \<psi>_eq assms by auto
  hence "s = -4*n+t" using distinct_residus[of A n k "-4*n+t" s] "14" ineq assms by auto
  then show ?thesis by simp
next
  case 24
  have ineq: "-n \<le> t-4*n \<and> t-4*n \<le> n \<and> -n \<le> 2*n-s \<and> 2*n-s \<le> n" using "24" by auto
  have "\<psi>_int A (t-4*n) mod k = \<psi>_int A (2*n-s) mod k"
    using assms \<psi>_eq technical_lemma2[of n A k "-s"] technical_lemma2_part2[of n A k "-1" t]
      \<psi>_int_odd[of A "-s"] by (smt (z3) sun_lemma10_rec)
  hence "t-4*n = 2*n - s" using distinct_residus[of A n k "t-4*n" "2*n-s"] ineq assms by auto
  then show ?thesis by simp
next
  case 44
  have ineq: "-n \<le> s-4*n \<and> s-4*n \<le> n \<and> -n \<le> t-4*n \<and> t-4*n \<le> n" using "44" by auto
  have "\<psi>_int A (s-4*n) mod k = \<psi>_int A (t-4*n) mod k"
    using assms \<psi>_eq technical_lemma2_part2[of n A k "-1" s] technical_lemma2_part2[of n A k "-1" t]
    by (smt (z3) sun_lemma10_rec)
  then show ?thesis using distinct_residus[of A n k "t-4*n" "s-4*n"] ineq assms by auto
qed
qed

lemma mod_pos:
  fixes k::int and n::int
  assumes "n > 0"
  shows "0 \<le> k mod n \<and> k mod n < n"
  by (simp add: assms)

lemma lesser_4n_to_all:
  fixes A::int and n::int and s::int and t::int and k::int
  assumes "A > 2" and "n > 3" and "\<chi>_int A n = 2*k"
  shows "(\<psi>_int A s mod k = \<psi>_int A t mod k)
      \<Longrightarrow> (s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n))"
proof -
  assume hyp_true: "\<psi>_int A s mod k = \<psi>_int A t mod k"
  have dvd_mod: "a dvd b \<Longrightarrow> l mod b = m mod b \<Longrightarrow> l mod a = m mod a" for a::int and b and l and m
    by (metis mod_mod_cancel)
  define s0 where "s0 = s mod (4*n)"
  define t0 where "t0 = t mod (4*n)"
  have hyp_s: "s mod (4*n) = s0 mod (4*n) \<and> 0 \<le> s0 \<and> s0 < 4*n" unfolding s0_def using assms by auto
  have hyp_t: "t mod (4*n) = t0 mod (4*n) \<and> 0 \<le> t0 \<and> t0 < 4*n" unfolding t0_def using assms by auto
  have "(s+t) mod (4*n) = (s0+t0) mod (4*n)" using hyp_s hyp_t mod_add_cong[of s "4*n" s0 t t0]
    by auto
  hence impl: "(s0 mod (4*n) = t0 mod (4*n) \<or> (s0+t0) mod (4*n) = (2*n) mod (4*n))
      \<Longrightarrow> (s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n))"
    using hyp_s hyp_t by auto
  obtain qs where qs_def: "s = 4*n*qs + s0" using s0_def by (metis mult_div_mod_eq)
  obtain qt where qt_def: "t = 4*n*qt + t0" using t0_def by (metis mult_div_mod_eq)
  have "\<psi>_int A s mod k = \<psi>_int A s0 mod k \<and> \<psi>_int A t mod k = \<psi>_int A t0 mod k"
    using technical_lemma2_part2[of n A k qs s0] qs_def assms 
    technical_lemma2_part2[of n A k qt t0] qt_def by auto
  hence "\<psi>_int A s0 mod k = \<psi>_int A t0 mod k" using hyp_true by auto
  then have "s0 mod (4*n) = t0 mod (4*n) \<or> (s0+t0) mod (4*n) = (2*n) mod (4*n)"
    using case_lesser_than_4n[of A n k s0 t0] assms hyp_s hyp_t by auto
  thus "s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n)" using impl by auto
qed

lemma sun_lemma10_dir:
  fixes A::int and n::int and s::int and t::int and k::int
  assumes "A > 2" and "n > 3" and "\<chi>_int A n = 2*k"
  shows "(\<psi>_int A s mod k = \<psi>_int A t mod k)
      \<Longrightarrow> (s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = (2*n) mod (4*n))"
  using assms lesser_4n_to_all[of A n k s t] by simp

lemma (in bridge_variables) sun_lemma24:
  fixes A::int and B::int and C::int and x::int and y::int
  assumes "abs A \<ge> 2"
  shows "is_square (D_f A C * F_ACx A C x * I_ABCxy A B C x y) = (is_square (D_f A C)
      \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y))"
proof -
  have converse: "(is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y))
      \<Longrightarrow> is_square (D_f A C * F_ACx A C x * I_ABCxy A B C x y)"
  proof -
    assume "(is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y))"
    then obtain d f i where "D_f A C = d^2 \<and> F_ACx A C x = f^2 \<and> I_ABCxy A B C x y = i^2"
      by (auto simp add: is_square_def)
    hence "D_f A C * F_ACx A C x * I_ABCxy A B C x y = (d*f*i)^2" by (auto simp add: algebra_simps)
    thus ?thesis using is_square_def by auto
  qed
  have direct: "is_square (D_f A C * F_ACx A C x * I_ABCxy A B C x y)
      \<Longrightarrow> ((is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y)))"
  proof -
    assume hyp: "is_square (D_f A C * F_ACx A C x * I_ABCxy A B C x y)"
    have square_decomp: "is_square (a*b) \<and> coprime a b \<and> a \<ge> 0 \<and> b \<ge> 0 \<Longrightarrow> is_square a \<and> is_square b"
      for a b :: int
    proof -
      assume hypo: "is_square (a*b) \<and> coprime a b \<and> a \<ge> 0 \<and> b \<ge> 0"
      then obtain k where k_def: "a*b = k^2" using is_square_def by auto
      define c where "c = gcd a k"
      define d where "d = gcd b k"
      have eq1: "c*c dvd a*b \<and> d*d dvd a*b" using c_def d_def k_def power2_eq_square[of k]
        by (auto simp add: mult_dvd_mono)
      have "coprime c b \<and> coprime d a" using c_def d_def hypo coprime_divisors[of c a b b]
          coprime_divisors[of d b a a] by (simp add: coprime_commute)
      hence cop: "coprime (c*c) b \<and> coprime (d*d) a" by auto
      hence eq2: "c*c dvd a \<and> d*d dvd b" using eq1 by (meson coprime_dvd_mult_left_iff euclids_lemma)
      have "k dvd a*b" using k_def by auto
      hence "k dvd c*d" using c_def d_def apply simp
        by (metis (no_types, lifting) division_decomp dvd_triv_left dvd_triv_right gcd_greatest_iff mult_dvd_mono)
      hence "a*b dvd (c*d*c*d)" using k_def power2_eq_square[of k] by auto
      hence "a dvd (d*d)*(c*c) \<and> b dvd (c*c)*(d*d)" by (metis dvd_mult_right mult.assoc mult.commute)
      hence "a dvd (c*c) \<and> b dvd (d*d)"
        using cop euclids_lemma[of a "d*d" "c*c"] coprime_commute[of a "d*d"]
          euclids_lemma[of b "c*c" "d*d"] coprime_commute[of b "c*c"] by auto
      hence "a=c*c \<and> b=d*d"
        using eq2 hypo zdvd_antisym_nonneg zero_le_square
        by simp
      thus ?thesis using is_square_def[of a] is_square_def[of b] power2_eq_square[of c]
          power2_eq_square[of d] by metis
    qed
    have copFD: "coprime (F_ACx A C x) (D_f A C)"
    proof -
      have "F_ACx A C x mod (D_f A C) = (4*(A^2-4)*(C^2*D_f A C*x)^2+1) mod (D_f A C)"
        unfolding F_ACx_def F_f_def E_ACx_def E_f_def by simp
      hence "F_ACx A C x mod (D_f A C) = (4*(A^2-4)*(C^2*x)^2*D_f A C*D_f A C+1) mod (D_f A C)"
        using power_mult_distrib[of "C^2*x" "D_f A C" 2] power2_eq_square[of "D_f A C"]
        by (auto simp add: algebra_simps)
      hence "F_ACx A C x mod (D_f A C) = 1 mod (D_f A C)" by auto
      thus ?thesis by (metis coprimeI coprime_mod_left_iff mod_by_0)
    qed
    have copID: "coprime (I_ABCxy A B C x y) (D_f A C)"
    proof -
      have "G_ACx A C x mod (D_f A C)
      = (1 + (C*F_ACx A C x)* D_f A C - 2*(A+2)*(A-2)^2*(C^2*D_f A C*x)^2) mod (D_f A C)" 
        unfolding G_ACx_def G_f_def E_ACx_def E_f_def by (auto simp add: algebra_simps)
      hence "G_ACx A C x mod (D_f A C)
      = (1 + (C*F_ACx A C x)* D_f A C - 2*(A+2)*(A-2)^2*(C^2*x)^2*D_f A C* D_f A C) mod (D_f A C)"
        using power2_eq_square[of "D_f A C"] power_mult_distrib[of "D_f A C"]
        by (auto simp add: algebra_simps)
      hence "G_ACx A C x mod (D_f A C) = 1 mod (D_f A C)" by (smt (z3) mod_mult_self3)
      hence "(G_ACx A C x^2 - 1) mod (D_f A C) = 0 mod (D_f A C)"
        by (metis cancel_comm_monoid_add_class.diff_cancel mod_diff_left_eq power_mod power_one)
      hence "((G_ACx A C x^2 - 1)*H_ABCxy A B C x y) mod (D_f A C) = 0 mod (D_f A C)" by auto
      hence "I_ABCxy A B C x y mod (D_f A C) = 1 mod (D_f A C)" unfolding I_ABCxy_def I_f_def
        using mod_add_cong[of "(G_ACx A C x^2 - 1)*H_ABCxy A B C x y" "D_f A C" 0 1 1] apply simp
        by (metis (no_types) \<open>((G_ACx A C x)\<^sup>2 - 1) mod D_f A C = 0 mod D_f A C\<close> mod_add_left_eq mod_mult_left_eq mod_mult_self2_is_0 mod_mult_self4 mult_numeral_1)
      thus ?thesis by (metis coprimeI coprime_mod_left_iff mod_by_0)
    qed
    have "2*G_ACx A C x mod (F_ACx A C x)
      = (2*C*D_f A C * F_ACx A C x + (2-4*(A+2)*(A-2)^2*E_ACx A C x^2)) mod (F_ACx A C x)"
      unfolding G_ACx_def G_f_def by (auto simp add: algebra_simps)
    hence "2*G_ACx A C x mod (F_ACx A C x) = (2-4*(A+2)*(A-2)^2*E_ACx A C x^2) mod (F_ACx A C x)"
      by auto
    hence "2*G_ACx A C x mod (F_ACx A C x) = (2-4*(A^2-4)*E_ACx A C x^2 * (A-2)) mod (F_ACx A C x)"
      by (auto simp add: algebra_simps power2_eq_square)
    hence "2*G_ACx A C x mod (F_ACx A C x) = (2-(F_ACx A C x-1) * (A-2)) mod (F_ACx A C x)"
      unfolding F_ACx_def F_f_def by auto
    hence "2*G_ACx A C x mod (F_ACx A C x) = (A - (A-2)*F_ACx A C x) mod (F_ACx A C x)"
      by (auto simp add: algebra_simps)
    hence A_eq_2G_modF:  "2*G_ACx A C x mod (F_ACx A C x) = A mod (F_ACx A C x)"
      by (metis add.commute diff_add_cancel mod_mult_self3)
    have copIF: "coprime (I_ABCxy A B C x y) (F_ACx A C x)"
    proof -
      have "H_ABCxy A B C x y mod (F_ACx A C x) = C mod (F_ACx A C x)"
        unfolding H_ABCxy_def H_f_def by auto
      hence "H_ABCxy A B C x y^2 mod (F_ACx A C x) = C^2 mod (F_ACx A C x)" by (metis power_mod)
      hence H_eqC: "((A^2-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x) = D_f A C mod (F_ACx A C x)"
        using mod_mult_cong[of "A^2-4" "F_ACx A C x" "A^2-4" "H_ABCxy A B C x y^2" "C^2"]
        unfolding D_f_def by (metis (no_types) add.commute mod_add_right_eq)
      have "((2*G_ACx A C x)*(2*G_ACx A C x)-4) mod (F_ACx A C x) = (A*A-4) mod (F_ACx A C x)"
        using A_eq_2G_modF by (metis (no_types) mod_diff_left_eq mod_mult_left_eq mod_mult_right_eq)
      hence A_eq2G: "(((2*G_ACx A C x)*(2*G_ACx A C x)-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x)
          = ((A*A-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x)"
        using mod_mult_cong[of "((2*G_ACx A C x)*(2*G_ACx A C x)-4)" "F_ACx A C x" "A*A-4"
            "H_ABCxy A B C x y^2" "H_ABCxy A B C x y^2"]
        by (smt (verit, ccfv_SIG) add.commute mod_add_right_eq)
      have "4*I_ABCxy A B C x y mod (F_ACx A C x)
          = 4*((G_ACx A C x^2-1)*H_ABCxy A B C x y^2 +1) mod (F_ACx A C x)"
        unfolding I_ABCxy_def I_f_def by auto
      hence "4*I_ABCxy A B C x y mod (F_ACx A C x)
          = (((2*G_ACx A C x)^2-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x)"
        using power_mult_distrib[of 2 "G_ACx A C x" 2] by (auto simp add: algebra_simps)
      hence "4*I_ABCxy A B C x y mod (F_ACx A C x)
          = (((2*G_ACx A C x)*(2*G_ACx A C x)-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x)"
        by (auto simp add: power2_eq_square)
      hence "4*I_ABCxy A B C x y mod (F_ACx A C x) = ((A*A-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x)"
        using A_eq2G by auto
      hence "4*I_ABCxy A B C x y mod (F_ACx A C x) = ((A^2-4)*H_ABCxy A B C x y^2 +4) mod (F_ACx A C x)"
        using power2_eq_square[of A] by auto
      hence "4*I_ABCxy A B C x y mod (F_ACx A C x) = D_f A C mod (F_ACx A C x)" using H_eqC by auto
      hence "gcd (4*I_ABCxy A B C x y) (F_ACx A C x) = gcd (D_f A C) (F_ACx A C x)"
        by (metis gcd_red_int)
      hence "coprime (4*I_ABCxy A B C x y) (F_ACx A C x)"
        using copFD by (metis coprime_iff_gcd_eq_1 gcd.commute)
      then show ?thesis by simp
    qed
    have A_pos: "A^2-4 \<ge> 0"
      using assms power2_eq_square[of "abs A"] mult_mono[of 2 "abs A" 2 "abs A"] by auto
    hence D_pos: "D_f A C \<ge> 1" unfolding D_f_def by auto
    have F_pos: "F_ACx A C x \<ge> 1" unfolding F_ACx_def F_f_def using A_pos by auto
    obtain k where "D_f A C * F_ACx A C x * I_ABCxy A B C x y = k^2" using hyp is_square_def by auto
    hence I_pos: "I_ABCxy A B C x y \<ge> 0" using D_pos F_pos
      by (smt (verit, ccfv_SIG) mult_pos_neg mult_pos_pos zero_le_power2)
    have copDF_I: "coprime (D_f A C * F_ACx A C x) (I_ABCxy A B C x y)"
      using copID copIF coprime_commute by auto
    hence "is_square (I_ABCxy A B C x y) \<and> is_square (D_f A C * F_ACx A C x)"
      using I_pos D_pos F_pos square_decomp[of "D_f A C * F_ACx A C x" "I_ABCxy A B C x y"] hyp
      by auto
    then show ?thesis
      using square_decomp[of "D_f A C" "F_ACx A C x"]  D_pos F_pos copFD coprime_commute by auto
  qed
  show ?thesis using direct converse by argo
qed

end
