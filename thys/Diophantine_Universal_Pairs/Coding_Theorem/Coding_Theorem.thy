theory Coding_Theorem
  imports Coding_Theorem_Definitions "../Coding/Tau_Reduction" "../Coding/Masking" 
    "../Coding/Lemma_1_8"
begin


lemma digit_sum_bound_int:
  fixes f::"nat \<Rightarrow> int"
  assumes "1 < b" and "\<forall>i\<in>{0..q}. f i < b"
  shows "(\<Sum>i=0..q. f i * b^i) < b^(Suc q)"
using assms(2)
proof (induct q)
  case 0 thus ?case by simp
next
  case (Suc q)
  have "(\<Sum>i=0..Suc q. f i * b^i) = (\<Sum>i=0..q. f i * b^i) + f (Suc q) * b^(Suc q)"
    by simp
  also have "... < b^(Suc q) + f (Suc q) * b^(Suc q)"
    using Suc by auto
  also have "... \<le> b^(Suc q) + (b-1) * b^(Suc q)"
    using Suc.prems assms(1) by auto
  also have "... = b^(Suc (Suc q))"
    by (metis add.commute add_diff_eq cancel_comm_monoid_add_class.diff_cancel group_cancel.rule0 
        int_distrib(1) lambda_one power_Suc) 
  finally show ?case .
qed

subsection \<open>Proof\<close>
                                   
locale coding_theorem = coding_variables + 
  assumes a_nonneg: "a \<ge> 0"
      and f_pos: "f > 0"
      and b_power2: "is_power2 b"
      and \<delta>_pos: "\<delta> > 0"
begin

text \<open>b being a power of 2 implies that the following are also powers of 2: \<close>
lemma \<B>_power2: "is_power2 \<B>"
  unfolding \<B>_def \<beta>_def using b_power2 by simp
lemma N0_power2: "is_power2 N0"
  unfolding N0_def using \<B>_power2 by simp
lemma N1_power2: "is_power2 N1"
  unfolding N1_def using \<B>_power2 by simp 
lemma N_power2: "is_power2 N"
  unfolding N_def using N0_power2 N1_power2 by simp
lemma Ng_power2: "is_power2 N"
  by (simp add: N_power2)

lemma \<B>_ge_2: "\<B> \<ge> 2"
  unfolding \<B>_def \<beta>_def using r_pos[OF \<delta>_pos] is_power2_ge1[OF b_power2] apply simp
  by (smt (verit, best) mult_pos_pos one_le_power pos_zmult_eq_1_iff self_le_power)

lemma \<B>_even: "2 dvd \<B>"
  using \<B>_power2 unfolding is_power2_def using \<B>_ge_2
  by (metis Suc_eq_plus1 dvd_refl even_power mult_cancel_left1 not_gr_zero numeral_le_iff 
      numerals(1) of_nat_1 of_nat_numeral plus_nat.add_0 power.simps(2) power_one_right 
      semiring_norm(69) zero_neq_numeral)

lemma b_le_\<B>: "b \<le> \<B>"
  unfolding \<B>_def \<beta>_def apply simp 
  using \<delta>_pos is_power2_ge1[OF b_power2]
  by (smt (verit) mult_le_cancel_right1 self_le_power zero_less_power)

lemma M_bound: "0 \<le> M \<and> M < N0"
proof
  show "0 \<le> M"
  proof -
    have "m i \<ge> 0" for i
      unfolding m_def using b_le_\<B> is_power2_ge1[OF \<B>_power2] by simp
    hence "m i * \<B>^i \<ge> 0" for i
      using is_power2_ge1[OF \<B>_power2] by simp
    thus ?thesis
      unfolding M_def by (meson sum_nonneg)
  qed
  
  show "M < N0"
  proof -
    have "m i < \<B>" for i
      unfolding m_def using is_power2_ge1[OF b_power2] by simp
    thus ?thesis
      unfolding M_def N0_def n_def using digit_sum_bound_int \<B>_ge_2 by simp
  qed
qed

context
  fixes g::int
  assumes g_lower_bound: "0 \<le> g" 
      and g_upper_bound: "g < 2 * b * \<B>^(n \<nu>)"
begin

lemma g_lt_N0: "g < N0"
proof -
  have "g < 2 * b * \<B>^(n \<nu>)"
    using g_upper_bound by simp
  also have "... \<le> \<B> * \<B>^(n \<nu>)"
  proof -
    have "2 \<le> \<beta>"
      by (metis \<beta>_def add_leE numeral_Bit0 one_le_numeral r_pos[OF \<delta>_pos] self_le_power) 
    hence "2 * b \<le> \<B>"
      unfolding \<B>_def using is_power2_ge1[OF b_power2] \<delta>_pos
      by (metis int_nat_eq int_one_le_iff_zero_less less_irrefl_nat mult_mono' of_nat_0_le_iff 
          of_nat_le_iff of_nat_numeral self_le_power zless_nat_eq_int_zless)
    thus ?thesis
      using is_power2_ge1[OF \<B>_power2] by simp
  qed     
  also have "... = N0"
    unfolding N0_def n_def
    using power_add N0_def by simp
  finally show ?thesis .
qed

lemma c_bound: "abs (c g) < 3 * b * \<B>^(n \<nu>)"
proof -
  have "a \<le> 6*a+3" 
    using a_nonneg by auto
  also have "... \<le> (6*a+3) * f"
    using f_pos a_nonneg by auto
  finally have 0: "1 + a \<le> b"
    unfolding b_def by simp
  
  have "abs (c g) = abs (1 + a * \<B> + g)"
    using c_def by simp
  also have "... = 1 + a * \<B> + g"
    using is_power2_ge1[OF \<B>_power2] g_lower_bound a_nonneg by auto
  also have "... \<le> (1 + a) * \<B> + g"
    using is_power2_ge1[OF \<B>_power2]
    by (smt (verit, ccfv_SIG) mult_right_cancel mult_right_mono)
  also have "... \<le> b * \<B> + g"
    by (smt (verit, best) 0 \<B>_power2 is_power2_ge1 mult_right_mono)
  also have "... \<le> b * \<B>^(n \<nu>) + g"
    unfolding n_def using is_power2_ge1 \<B>_power2 "0" a_nonneg self_le_power 
    by fastforce
  finally show ?thesis
    using g_upper_bound by auto
qed

lemma D_bound: "abs D \<le> fact \<delta> * \<L> * \<B>^(n (\<nu>+1))"
proof -
  have 0: "i\<in>\<delta>_tuples \<Longrightarrow> D_precoeff i \<le> int (fact \<delta>)" for i
    unfolding D_precoeff_def \<delta>_tuples_def using mchoose_le of_nat_mono by fastforce

  have "D_exponent i \<le> n (\<nu>+1)" for i
    unfolding D_exponent_def by simp
  hence 1: "\<B>^(D_exponent i) \<le> \<B>^(n (\<nu>+1))" for i
    using is_power2_ge1[OF \<B>_power2] power_increasing by blast

  have "abs D \<le> (\<Sum>i\<in>\<delta>_tuples. abs (D_precoeff i * P_coeff i * \<B>^(D_exponent i)))"
    using D_def \<delta>_tuples_finite by simp
  also have "... = (\<Sum>i\<in>\<delta>_tuples. abs (D_precoeff i) * abs (P_coeff i) * (abs \<B>)^(D_exponent i))"
    using abs_mult by (metis (no_types, opaque_lifting) power_abs)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. D_precoeff i * abs (P_coeff i) * \<B>^(D_exponent i))"
    using is_power2_ge1[OF \<B>_power2] D_precoeff_def by auto
  also have "... \<le> (\<Sum>i\<in>\<delta>_tuples. fact \<delta> * abs (P_coeff i) * \<B>^(n (\<nu>+1)))"
  proof -
    { fix i assume assm: "i\<in>\<delta>_tuples"
      have "0 \<le> \<B>^(D_exponent i)" 
        using is_power2_ge1[OF \<B>_power2] by auto
      moreover have "0 \<le> D_precoeff i" 
        using D_precoeff_def by auto
      ultimately have "D_precoeff i * abs (P_coeff i) * \<B>^(D_exponent i) \<le> 
        fact \<delta> * abs (P_coeff i) * \<B>^(n (\<nu>+1))"
        using "0"[OF assm] 1 by (simp add: mult_mono') }
    thus ?thesis
      using sum_mono by meson
  qed
  also have "... = fact \<delta> * (\<Sum>i\<in>\<delta>_tuples. abs (P_coeff i)) * \<B>^(n (\<nu>+1))"
    using sum_distrib_left sum_distrib_right by metis
  finally show ?thesis
    unfolding \<L>_def by simp
qed

lemma c_\<delta>_D_bound: "2 * abs ((c g)^\<delta> * D) \<le> \<B>^((2*\<delta>+1)*n \<nu> + 1)"
proof -
  have 0: "\<beta> > int (2 * fact \<delta> * \<L> * 3^\<delta>)"
  proof -
    have "3^\<delta> \<le> (\<nu>+3)^\<delta>"
      by (simp add: power_mono)
    thus ?thesis
      using \<beta>_lower_bound
      by (smt (verit, best) nat_less_as_int nat_mult_less_cancel_disj not_less)
  qed

  have "2 * abs ((c g)^\<delta> * D) = 2 * (abs (c g))^\<delta> * abs D"
    by (simp add: abs_mult power_abs) 
  also have "... \<le> 2 * (3 * b * \<B>^(n \<nu>))^\<delta> * (fact \<delta> * \<L> * \<B>^(n (\<nu>+1)))"
    using D_bound c_bound by (simp add: \<delta>_pos mult_mono)
  also have "... = 2 * (3^\<delta> * b^\<delta> * \<B>^(n \<nu> * \<delta>)) * (fact \<delta> * \<L> * \<B>^(n (\<nu>+1)))"
    using power_mult power_mult_distrib by (metis (no_types, opaque_lifting))
  also have "... = (2 * fact \<delta> * \<L> * 3^\<delta>) * (b^\<delta> * \<B>^((2*\<delta>+1) * n \<nu>))"
  proof -
    have "X^(n \<nu> * \<delta>) * X^(n (\<nu>+1)) = X^((2*\<delta>+1) * n \<nu>)" for X::int
      using power_add n_def
      by (smt (verit) add_mult_distrib2 left_add_twice mult.commute power_one_right)
    thus ?thesis
      by simp
  qed 
  also have "... \<le> \<beta> * (b^\<delta> * \<B>^((2*\<delta>+1) * n \<nu>))"
    using 0 is_power2_ge1 b_power2 \<B>_power2
    by (smt (verit, del_insts) mult_le_0_iff mult_right_mono zero_less_power)
  also have "... = \<B> * \<B>^((2*\<delta>+1) * n \<nu>)"
    using \<B>_def by simp
  finally show ?thesis 
    using power_add by simp
qed

lemma K_bound: "0 \<le> K g \<and> 2 * K g < 3 * \<B>^((2*\<delta>+1)*n \<nu> + 1)"
proof
  define K2 :: int where "K2 \<equiv> (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. of_nat (\<beta> div 2) * b^\<delta> * \<B>^i)"
  have K_def_alt: "K g = (c g)^\<delta> * D + K2"
    using K2_def K_def by simp
 
  have K2_def_alt: "K2 = (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. (\<B> div 2) * \<B>^i)"
  proof -
    have "K2 = (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. (\<beta> div 2) * b^\<delta> * \<B>^i)"
      using K2_def by simp
    also have "... = (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. (\<B> div 2) * \<B>^i)" 
    proof -
      have "2 dvd \<beta>"
        unfolding \<beta>_def using r_pos[OF \<delta>_pos] by simp
      hence "(\<beta> div 2) * b^\<delta> = \<B> div 2"
        by (simp add: \<B>_def dvd_div_mult zdiv_int)
      thus ?thesis 
        using sum.cong by auto
     qed
     finally show ?thesis .
  qed

  have K2_bound: "\<B>^((2*\<delta>+1) * n \<nu> + 1) \<le> 2 * K2 \<and> K2 < \<B>^((2*\<delta>+1) * n \<nu> + 1)"
  proof 
    have "K2 = (\<Sum>i=0..<(2*\<delta>+1)*n \<nu>. (\<B> div 2) * \<B>^i) + (\<B> div 2) * \<B>^((2*\<delta>+1) * n \<nu>)"
      unfolding K2_def_alt using n_def
      by (smt (verit) atLeastLessThanSuc_atLeastAtMost sum.atLeast0_lessThan_Suc)
    also have "... \<ge> (\<B> div 2) * \<B>^((2*\<delta>+1) * n \<nu>)"
    proof -
      have "(\<B> div 2) * \<B>^i \<ge> 0" for i
        using is_power2_ge1[OF \<B>_power2] by auto
      thus ?thesis
        using sum_nonneg by (smt (verit, ccfv_threshold))
    qed
    finally have "2 * K2 \<ge> 2 * (\<B> div 2) * \<B>^((2*\<delta>+1) * n \<nu>)"
      by simp
    thus "2 * K2 \<ge> \<B>^((2*\<delta>+1) * n \<nu> + 1)"
      using \<B>_even power_add by simp

    show "K2 < \<B>^((2*\<delta>+1)*n \<nu> + 1)"
    proof -
      have "\<B> div 2 < \<B>"
        using \<B>_ge_2 by simp
      thus ?thesis
        unfolding K2_def_alt using digit_sum_bound_int \<B>_ge_2 by simp
    qed
  qed

  show "0 \<le> K g" 
    unfolding K_def_alt using c_\<delta>_D_bound K2_bound by simp linarith 
  show "2 * (K g) < 3 * \<B>^((2*\<delta>+1)*n \<nu> + 1)"
    unfolding K_def_alt using c_\<delta>_D_bound K2_bound by simp linarith
qed

text \<open>technical condition 2.7, first part\<close>
lemma T_bound: "0 \<le> T \<and> T < N"
proof 
  show "0 \<le> T"
  proof -
    have "T = M + (\<B> - 2) * \<B>^(n (\<nu>+1)) * N0"
      using T_def n_def by simp
    thus ?thesis
      using M_bound \<B>_ge_2 is_power2_ge1[OF N0_power2] by auto
  qed
  
  have 0: "1 + (\<B> - 2) * \<B>^(n (\<nu>+1)) \<le> N1"
  proof - 
    have "1 + (\<B> - 2) * \<B>^(n (\<nu>+1)) \<le> 2 * \<B>^(n (\<nu>+1)) + (\<B> - 2) * \<B>^(n (\<nu>+1))"    
      using is_power2_ge1[OF \<B>_power2] by (smt (z3) one_le_power)
    also have "... = \<B>^(n (\<nu>+1) + 1)"
      using \<B>_ge_2 by (metis add.commute diff_add_cancel int_distrib(1) power_add power_one_right)
    also have "... \<le> 4 * \<B>^((2*\<delta>+1) * n \<nu> + 1)"
    proof - 
      have "n (\<nu>+1) + 1 \<le> (2*\<delta>+1) * n \<nu> + 1"
        unfolding n_def by simp
      thus ?thesis 
        using is_power2_ge1[OF \<B>_power2] power_increasing by (smt (verit, ccfv_SIG) K_bound)
    qed
    also have "... = N1"
      using N1_def n_def by simp
    finally show ?thesis .
  qed

  show "T < N"
  proof -
    have "T < N0 + (\<B> - 2) * \<B>^(n (\<nu>+1)) * N0"
      using T_def M_bound n_def by simp
    also have "... = (1 + (\<B> - 2) * \<B>^(n (\<nu>+1))) * N0"
      by (simp add: algebra_simps)      
    also have "... \<le> N1 * N0"
      using 0 is_power2_ge1[OF N0_power2] by simp
    also have "... = N"
      using N_def by simp
    finally show ?thesis .
  qed
qed

text \<open>technical condition 2.7, second part\<close>
lemma S_bound: "0 \<le> S g \<and> S g < N"
proof 
  show "0 \<le> S g"
  proof -
    have "S g = g + 2 * K g * N0"
      using S_def by simp
    thus ?thesis 
      using K_bound g_lower_bound is_power2_ge1[OF N0_power2] by simp
  qed

  have 0: "g < \<B>^((2*\<delta>+1)*n \<nu> + 1)"
  proof -
    have "g < \<B>^(n \<nu> + 1)"
      using g_lt_N0 N0_def n_def by simp
    also have "... \<le> \<B>^((2*\<delta>+1)*n \<nu> + 1)"
    proof -
      have "n \<nu> + 1 \<le> (2*\<delta>+1)*n \<nu> + 1"
        unfolding n_def by simp
      thus ?thesis 
        using is_power2_ge1[OF \<B>_power2] power_increasing by blast
    qed
    finally show ?thesis .
  qed

  show "S g < N"
  proof -
    have "S g = g + 2 * K g * N0"
      using S_def by simp
    also have "... \<le> (g + 2 * K g) * N0"
    proof -
      have "g \<le> g * N0"
        using g_lower_bound is_power2_ge1[OF N0_power2]
        by (simp add: mult_le_cancel_left1)
      thus ?thesis 
        by (simp add: algebra_simps)
    qed
    also have "... < N1 * N0"
    proof -
      have "g + 2 * K g < N1"
        unfolding N1_def using 0 K_bound n_def by simp
      thus ?thesis
        using is_power2_ge1[OF N0_power2] by auto
    qed
    also have "... = N"
      using N_def by simp
    finally show ?thesis .
  qed 
qed

text \<open>Technical condition 2.8\<close>
lemma tau_S_T_decomp: "\<tau> (nat (S g)) (nat (T)) = 
  \<tau> (nat g) (nat (M)) + \<tau> (nat (2 * K g)) (nat ((\<B> - 2) * \<B>^(n (\<nu>+1))))"
proof -
  have 0: "nat (S g) = nat g + nat (K g) * nat (2 * N0)"
  proof -
    have "nat (S g) = nat (g + 2 * K g * N0)"
      using S_def by simp
    also have "... = nat g + 2 * nat (K g) * nat (N0)"
      using g_lower_bound K_bound is_power2_ge1[OF N0_power2]
      by (simp add: nat_add_distrib nat_mult_distrib)
    finally show ?thesis 
      by auto
  qed
  
  have 1: "nat (T) = nat (M) + nat ((\<B> div 2 - 1) * \<B>^(n (\<nu>+1))) * nat (2 * N0)"
  proof -
    have "nat (T) = nat (M + (\<B> - 2) * \<B>^(n (\<nu>+1)) * N0)"
      using T_def n_def by simp
    also have "... = nat (M + 2 * (\<B> div 2 - 1) * \<B>^(n (\<nu>+1)) * N0)"
      using \<B>_even by simp
    also have "... = nat (M) + nat ((\<B> div 2 - 1) * \<B>^(n (\<nu>+1))) * nat (2 * N0)"
      using \<B>_ge_2 M_bound is_power2_ge1[OF N0_power2]
      by (simp add: nat_power_eq nat_add_distrib nat_mult_distrib)
    finally show ?thesis .
  qed

  have "\<tau> (nat (S g)) (nat (T)) = 
    \<tau> (nat g + nat (K g) * nat (2 * N0)) 
      (nat (M) + nat ((\<B> div 2 - 1) * \<B>^(n (\<nu>+1))) * nat (2 * N0))"
    using 0 1 by metis
  also have "... = \<tau> (nat g) (nat (M)) + \<tau> (nat (K g)) (nat ((\<B> div 2 - 1) * \<B>^(n (\<nu>+1))))"
  proof -
    obtain k where k_def: "nat (2 * N0) = 2^k"
      using N0_power2 is_power2_def by fastforce
    have "nat g + nat (M) < nat (2 * N0)"
      using M_bound g_lt_N0 by auto
    thus ?thesis 
      using count_carries_add_shift_no_overflow k_def by metis
  qed 
  also have "... =  \<tau> (nat g) (nat (M)) + \<tau> (nat (2 * K g)) (nat ((\<B> - 2) * \<B>^(n (\<nu>+1))))"
  proof -
    have 0: "2 * nat (K g) = nat (2 * K g)"
      by simp
    have 1: "\<B> - 2 = 2 * (\<B> div 2 - 1)"
      using \<B>_even by simp
    have 2: "2 * nat ((\<B> div 2 - 1) * \<B>^(n (\<nu>+1))) = nat ((\<B> - 2) * \<B>^(n (\<nu>+1)))"
      unfolding 1 by linarith
    show ?thesis
      using count_carries_even_even 0 2 by metis
  qed
  finally show ?thesis .
qed

end

text \<open>Helper lemmas for masking\<close>

lemma n_masking_lemma[simp]: 
  assumes "masking_lemma \<delta> \<nu> (nat \<B>) (nat b) C" 
  shows "masking_lemma.n \<delta> = n"
  unfolding n_def using masking_lemma.n_def assms by auto
 
lemma m_masking_lemma[simp]:
  assumes "masking_lemma \<delta> \<nu> (nat \<B>) (nat b) C" 
  shows "masking_lemma.m \<delta> \<nu> (nat \<B>) (nat b) j = m j"
proof -
  have 0: "int (nat \<B>) = \<B>" 
    using is_power2_ge1[OF \<B>_power2] by simp
  have 1: "int (nat b) = b" 
    using is_power2_ge1[OF b_power2] by simp
  have 2: "int (nat \<B> - nat b) = (\<B> - b)"
  proof -
    have "int (nat \<B> - nat b) = int (nat \<B>) - int (nat b)"
      using b_le_\<B> by auto
    thus ?thesis 
      using 0 1 by simp
  qed
  have 3: "int (nat \<B> - 1) = (\<B> - 1)"
  proof -
    have "1 \<le> nat \<B>"
      using is_power2_ge1[OF \<B>_power2] by auto
    thus ?thesis 
      using 0 by simp
  qed

  have "masking_lemma.m \<delta> \<nu> (nat \<B>) (nat b) j =
    (if j \<in> n ` {1..\<nu>} then int (nat \<B> - nat b) else int (nat \<B> - 1))"
    unfolding masking_lemma.m_def[OF assms] n_masking_lemma[OF assms] by auto
  also have "... = (if j \<in> n ` {1..\<nu>} then (\<B> - b) else (\<B> - 1))"
    using 2 3 by simp
  also have "... = m j"
    using m_def by simp
  finally show ?thesis .
qed

lemma M_masking_lemma[simp]:
  assumes "masking_lemma \<delta> \<nu> (nat \<B>) (nat b) C" 
  shows "masking_lemma.M \<delta> \<nu> (nat \<B>) (nat b) = nat M"
proof -
  have "masking_lemma.M \<delta> \<nu> (nat \<B>) (nat b) = (\<Sum>j=0..n \<nu>. m j * \<B>^j)"
  unfolding masking_lemma.M_def[OF assms] using is_power2_ge1[OF \<B>_power2] 
  unfolding n_masking_lemma[OF assms] m_masking_lemma[OF assms, symmetric] by auto
  thus ?thesis
    using M_def by auto
qed
 
text \<open>Helper lemmas to apply Lemma 1.8\<close>
text \<open>We can only apply Lemma 1.8 when g can be decomposed in base \<open>\<B>\<close> with digits \<open><b\<close>\<close>
context 
  fixes g :: int 
    and z :: "nat \<Rightarrow> int"
  assumes g_sum: "g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))"
      and z_bound: "\<forall>i. 0 \<le> z i \<and> z i < b" 
begin

text \<open>This is quite verbose but justified by the following lemma\<close>
definition z_list :: "nat list" where 
  "z_list \<equiv> nat a # map (nat \<circ> z \<circ> nat) [1..\<nu>]"

lemma z_list_nth_head: "z_list!0 = nat a"
  unfolding z_list_def by simp

lemma z_list_nth_tail: "1 \<le> i \<Longrightarrow> i \<le> \<nu> \<Longrightarrow> z_list!i = nat (z i)"
proof -
  assume "1 \<le> i" and "i \<le> \<nu>"
  then obtain j where j_def: "i = j + 1" and "j < \<nu>"
    using nat_le_iff_add by fastforce

  have "z_list!i = (map (nat \<circ> z \<circ> nat) [1..\<nu>])!j"
    unfolding z_list_def j_def by simp
  also have "... = (nat \<circ> z \<circ> nat) ([1..\<nu>]!j)"
    using List.nth_map \<open>j < \<nu>\<close> by simp
  also have "... = nat (z (j+1))"
    by (metis Suc_eq_plus1 \<open>i \<le> \<nu>\<close> add.commute comp_apply int_ops(4) j_def nat_int nth_upto 
        of_nat_mono)
  finally show ?thesis 
    using j_def by simp
qed

lemma length_z_list[simp]: "length z_list = \<nu>+1"
  unfolding z_list_def by auto

lemma \<delta>_lemma_1_8[simp]: "Lemma_1_8_Defs.\<delta> P = \<delta>"
  using Lemma_1_8_Defs.\<delta>_def \<delta>_def by simp

lemma \<nu>_lemma_1_8[simp]: "Lemma_1_8_Defs.\<nu> P = \<nu>"
  using Lemma_1_8_Defs.\<nu>_def \<nu>_def by simp

lemma n_lemma_1_8[simp]: "Lemma_1_8_Defs.n P = n"
  using Lemma_1_8_Defs.n_def n_def \<delta>_lemma_1_8 by auto

lemma insertion_z_assign[simp]: 
  "insertion (Lemma_1_8_Defs.z_assign z_list) P = insertion (z(0 := a)) P"
proof -
  have "i\<in>vars P \<Longrightarrow> Lemma_1_8_Defs.z_assign z_list i = (z(0 := a)) i" for i
  proof -
    assume "i\<in>vars P" 
    hence i_bound: "i \<le> \<nu>"
      unfolding \<nu>_def max_vars_def by (simp add: vars_finite)
    
    have "Lemma_1_8_Defs.z_assign z_list i = int (z_list !\<^sub>0 i)"
      unfolding Lemma_1_8_Defs.z_assign_def
      by (metis Suc_eq_plus1 i_bound le_imp_less_Suc length_map length_z_list nth0_nth nth_map)
    also have "... = int (z_list ! i)"
      using length_z_list i_bound by (simp add: nth0_nth)
    also have "... = int (if i = 0 then nat a else nat (z i))"
      using z_list_nth_head z_list_nth_tail i_bound by auto
    also have "... = (if i = 0 then a else z i)"
      using a_nonneg z_bound by auto
    also have "... = (z(0 := a)) i"
      by auto
    finally show ?thesis .
  qed
  thus ?thesis 
    using insertion_irrelevant_vars by metis
qed

lemma S_lemma_1_8[simp]:
  "int (Lemma_1_8_Defs.S P (nat \<B>)) = (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. int (\<beta> div 2) * b^\<delta> * \<B>^i)"
proof -
  have "int (Lemma_1_8_Defs.S P (nat \<B>)) = 
    (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. int (((nat \<B>) div 2) * (nat \<B>)^i))"
    unfolding Lemma_1_8_Defs.S_def Lemma_1_8_Defs.b_def \<delta>_lemma_1_8 n_lemma_1_8 \<nu>_lemma_1_8 by simp
  also have "... = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (\<B> div 2) * \<B>^i)"
  proof -
    have "(nat \<B>) div 2 = nat (\<B> div 2)"
      using \<B>_even by auto
    thus ?thesis 
      using is_power2_ge1[OF \<B>_power2] by auto
  qed
  also have "... = (\<Sum>i=0..(2*\<delta>+1) * n \<nu>. (\<B> div 2) * \<B>^i)"
    using atLeast0AtMost by presburger
  also have "... = (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. int (\<beta> div 2) * b^\<delta> * \<B>^i)"
  proof -
    have "\<B> div 2 = int (\<beta> div 2) * b^\<delta>"
      unfolding \<B>_def \<beta>_def by (simp add: dvd_div_mult r_pos[OF \<delta>_pos] zdiv_int)
    thus ?thesis 
      by auto
  qed
  finally show ?thesis .
qed

lemma c_lemma_1_8[simp]: 
  "insertion (Lemma_1_8_Defs.\<B>_assign (nat \<B>)) (Lemma_1_8_Defs.c P z_list) = a * \<B> + g"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>i\<le>\<nu>. int (z_list!i) * (Lemma_1_8_Defs.\<B>_assign (nat \<B>) (0::nat))^(n i))"
    unfolding Lemma_1_8_Defs.c_def Lemma_1_8_Defs.X_def n_lemma_1_8 \<nu>_lemma_1_8 
    by simp 
  also have "... = (\<Sum>i\<le>\<nu>. int (z_list!i) * \<B>^(n i))"
    unfolding Lemma_1_8_Defs.\<B>_assign_def using \<B>_ge_2 by simp
  also have "... = int (z_list!0) * \<B>^(n 0) + (\<Sum>i=1..\<nu>. int (z_list!i) * \<B>^(n i))"
    by (simp add: atLeastSucAtMost_greaterThanAtMost atMost_atLeast0 sum.head)
  also have "... = a * \<B> + (\<Sum>i=1..\<nu>. int (z_list!i) * \<B>^(n i))"
    using n_def z_list_def a_nonneg by auto
  also have "... = a * \<B> + g"
    unfolding g_sum using z_bound z_list_nth_tail by auto
  finally show ?thesis .
qed

lemma D_lemma_1_8[simp]: 
  "insertion (Lemma_1_8_Defs.\<B>_assign (nat \<B>)) (Lemma_1_8_Defs.D P) = D"
  (is "?lhs = ?rhs")
proof -
  have 0: "Lemma_1_8_Defs.D_precoeff P i = D_precoeff i" for i
    unfolding Lemma_1_8_Defs.D_precoeff_def D_precoeff_def by simp
  have 1: "Lemma_1_8_Defs.P_coeff P i = P_coeff i" for i
    unfolding Lemma_1_8_Defs.P_coeff_def P_coeff_def by simp
  have 2: "Lemma_1_8_Defs.D_exponent P i = D_exponent i" for i
    unfolding Lemma_1_8_Defs.D_exponent_def D_exponent_def by simp
  have 3: "Lemma_1_8_Defs.\<delta>_tuples P = \<delta>_tuples"
    unfolding Lemma_1_8_Defs.\<delta>_tuples_def \<delta>_tuples_def by simp
  
  have "?lhs = (\<Sum>i\<in>\<delta>_tuples. D_precoeff i * P_coeff i * (Lemma_1_8_Defs.\<B>_assign (nat \<B>) (0::nat))^(D_exponent i))"
    unfolding Lemma_1_8_Defs.D_def Lemma_1_8_Defs.X_def by (simp add: 0 1 2 3)
  also have "... = D"
    unfolding D_def Lemma_1_8_Defs.\<B>_assign_def using \<B>_ge_2 by simp
  finally show ?thesis .
qed

lemma R_lemma_1_8[simp]: 
  "insertion (Lemma_1_8_Defs.\<B>_assign (nat \<B>)) (Lemma_1_8_Defs.R P z_list) = (c g)^\<delta> * D"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (1 + a * \<B> + g)^\<delta> * D"
    unfolding Lemma_1_8_Defs.R_def by (simp add: algebra_simps)
  also have "... = (c g)^\<delta> * D" 
    unfolding c_def by simp
  finally show ?thesis .
qed

lemma K_lemma_1_8[simp]:
  "Lemma_1_8_Defs.K P (nat \<B>) z_list = K g"
  unfolding Lemma_1_8_Defs.K_def K_def by simp
  
lemma lemma_1_8_helper: 
  shows "insertion (z(0 := a)) P = 0 \<longleftrightarrow> \<tau> (nat (2 * K g)) (nat ((\<B>  - 2) * \<B>^(n (\<nu>+1)))) = 0"
    and "K g > \<B>^((2*\<delta>+1) * n \<nu>)" 
    and "K g < \<B>^((2*\<delta>+1) * n \<nu> + 1)"
proof -
  have z_sum_bound: "sum_list z_list < (\<nu>+1) * nat b"
  proof -
    have "sum_list z_list = (\<Sum>i=0..\<nu>. z_list!i)"  
      using sum_list_sum_nth length_z_list 
      by (metis Suc_eq_plus1 atLeastLessThanSuc_atLeastAtMost) 
    also have "... = z_list!0 + (\<Sum>i=1..\<nu>. z_list!i)"
      by (simp add: atLeastSucAtMost_greaterThanAtMost sum.head)
    also have "... = nat a + (\<Sum>i=1..\<nu>. nat (z i))"
      using z_list_nth_head z_list_nth_tail by auto 
    also have "... \<le> nat a + (\<Sum>i=1..\<nu>. nat b)"
      using z_bound by (smt (verit, del_insts) add_left_mono nat_le_eq_zle sum_mono)
    also have "... = nat a + card {1..\<nu>} * nat b"
      using sum_constant by auto
    also have "... = nat a + \<nu> * nat b"
      by auto
    also have "... < nat b + \<nu> * nat b"
      unfolding b_def by simp (smt (verit) mult_less_cancel_left2 a_nonneg f_pos)
    finally show ?thesis 
      by auto
  qed

  have \<B>_lower_bound: "2 * fact \<delta> * \<L> * (sum_list z_list + 1)^\<delta> < nat \<B>"
  proof -
    have 0: "(sum_list z_list + 1)^\<delta> < (\<nu>+3)^\<delta> * (nat b)^\<delta>"
    proof -
      have "sum_list z_list + 1 \<le> (\<nu>+1) * nat b"
        using z_sum_bound by auto
      also have "... < (\<nu>+3) * nat b"
        using is_power2_ge1[OF b_power2]
        by (smt (verit, ccfv_threshold) add_less_cancel_left mult.commute nat_mult_less_cancel_disj 
            one_less_numeral_iff semiring_norm(77) zero_less_nat_eq)
      finally show ?thesis
        using power_mult_distrib zero_le by (metis \<delta>_pos power_strict_mono)
    qed
    
    have "2 * fact \<delta> * \<L> * (sum_list z_list + 1)^\<delta> < 2 * fact \<delta> * \<L> * (\<nu>+3)^\<delta> * (nat b)^\<delta>"
      using 0 fact_ge_1 \<L>_pos[OF \<delta>_pos] by auto
    also have "... \<le> \<beta> * (nat b)^\<delta>"
      using \<beta>_lower_bound by auto
    also have "... = nat \<B>"
      unfolding \<B>_def using is_power2_ge1[OF b_power2] by (simp add: nat_mult_distrib nat_power_eq)
    finally show ?thesis .
  qed

  have 0: "Lemma_1_8 P (nat \<B>) (int \<L>) z_list"
    unfolding Lemma_1_8_def K_Nonnegative_def
    using \<B>_power2 is_power2_ge1 \<L>_ge_max_coeff[OF \<delta>_pos] \<delta>_pos \<L>_pos[OF \<delta>_pos]
          \<B>_lower_bound Lemma_1_8_axioms.intro \<B>_even even_nat_iff by auto
  show "K g > \<B>^((2*\<delta>+1) * n \<nu>)"
    using Lemma_1_8.lemma_1_8(2)[OF 0] \<B>_ge_2 by simp
  show "K g < \<B>^((2*\<delta>+1) * n \<nu> + 1)"
    using Lemma_1_8.lemma_1_8(3)[OF 0] \<B>_ge_2 by simp
  show "insertion (z(0 := a)) P = 0 \<longleftrightarrow> \<tau> (nat (2 * K g)) (nat ((\<B>  - 2) * \<B>^(n (\<nu>+1)))) = 0"
    using Lemma_1_8.lemma_1_8(1)[OF 0] \<B>_ge_2 nat_diff_distrib nat_mult_distrib nat_power_eq 
    by auto
qed 

end

lemma aux_sum_bound_reindex_n: 
  "0 \<le> (x::int) \<Longrightarrow> (\<Sum>i=0..q. x^(n i)) \<le> (\<Sum>i=0..n q. x^i)"
proof (induct q)
  case 0 thus ?case apply simp
    by (metis member_le_sum atLeastAtMost_iff dual_order.refl finite_atLeastAtMost zero_le 
        zero_le_power)
next
  case (Suc q) 

  have 0: "Suc (n q) \<le> n (Suc q)"
    unfolding n_def using \<delta>_pos by auto

  have "(\<Sum>i=0..Suc q. x^(n i)) = (\<Sum>i=0..q. x^(n i)) + x^(n (Suc q))"
    by simp
  also have "... \<le> (\<Sum>i=0..n q. x^i) + x^(n (Suc q))"
    using Suc by simp
  also have "... \<le> (\<Sum>i=0..n q. x^i) + (\<Sum>i=Suc(n q)..n (Suc q). x^i)"
    using 0 Suc.prems member_le_sum
    by (metis add.commute add_le_cancel_right atLeastAtMost_iff finite_atLeastAtMost order.refl 
         zero_le_power)
  also have "... = (\<Sum>i=0..n (Suc q). x^i)"
  proof -
    have "{0..n q} \<union> {Suc (n q)..n (Suc q)} = {0..n (Suc q)}"
      using 0 by auto
    moreover have "{0..n q} \<inter> {Suc (n q)..n (Suc q)} = {}"
      by auto
    ultimately show ?thesis 
      using sum.union_disjoint by (metis finite_atLeastAtMost)
  qed
  finally show ?case .
qed

lemma coding_theorem_direct: 
  "statement1_strong y \<Longrightarrow> (\<exists>g. statement2_strong g)"
proof
  assume assm: "statement1_strong y"
  
  have "1 < b"
    using assm unfolding statement1_strong_def statement1_weak_def 
    by (smt (verit, del_insts))

  have y_bound: "0 \<le> y i \<and> y i < b" for i
    using assm unfolding statement1_strong_def statement1_weak_def by auto
   
  define g where "g \<equiv> (\<Sum>i=1..\<nu>. y i * \<B>^(n i))"

  have g_lower_bound: "b \<le> g"
  proof -
    from assm obtain j where 0: "y j > 0" and j_1\<nu>: "j \<in> {1..\<nu>}"
      unfolding statement1_strong_def statement1_weak_def
      by (meson leD linorder_neqE_linordered_idom)
 
    have "g \<ge> y j * \<B>^(n j)"
      using assm member_le_sum[OF j_1\<nu>] unfolding statement1_strong_def statement1_weak_def 
      by (smt (verit, del_insts) b_le_\<B> finite_atLeastAtMost g_def mult_nonneg_nonneg mult_zero_left zero_le_power)
    hence "g \<ge> \<B>^(n j)" using 0 is_power2_ge1[OF \<B>_power2]
      by (smt (verit, ccfv_SIG) mult_le_cancel_right1 zero_less_power)
    hence "g \<ge> \<B>"
      unfolding n_def using is_power2_ge1[OF \<B>_power2]
      by (smt (verit, ccfv_SIG) \<delta>_pos add_gr_0 self_le_power zero_less_power)
    thus "g \<ge> b"
      using b_le_\<B> by simp
  qed

  have g_upper_bound: "g < b * \<B>^(n \<nu>)"
  proof -
    have 0: "y i * \<B>^(n i) \<le> (b - 1) * \<B>^(n i)" for i
      using y_bound is_power2_ge1[OF \<B>_power2] by auto
    
    have "g = (\<Sum>i\<in>{0<..\<nu>}. y i * \<B>^(n i))"
      unfolding g_def by (simp add: atLeastSucAtMost_greaterThanAtMost)
    also have "... \<le> y 0 * \<B>^(n 0) + (\<Sum>i\<in>{0<..\<nu>}. y i * \<B>^(n i))"
      using is_power2_ge1 \<B>_power2 b_power2 y_bound
      by (smt (verit, del_insts) mult_nonneg_nonneg zero_le_power)
    also have "... = (\<Sum>i\<in>{0..\<nu>}. y i * \<B>^(n i))"
      using sum.head[of "0" "\<nu>"] by (smt (verit) zero_le)
    also have "... \<le> (\<Sum>i\<in>{0..\<nu>}. (b - 1) * \<B>^(n i))"
      using 0 sum_mono by meson
    also have "... = (b - 1) * (\<Sum>i=0..\<nu>. \<B>^(n i))"
      using sum_distrib_left by metis
    also have "... \<le> (b - 1) * (\<Sum>i=0..n \<nu>. \<B>^i)"
      using aux_sum_bound_reindex_n is_power2_ge1[OF b_power2] \<B>_ge_2 by (simp add: mult_left_mono)
    also have "... \<le> (b - 1) * (\<Sum>i=0..<n \<nu>. \<B>^i) + (b - 1) * \<B>^(n \<nu>)"
      by (metis atLeastLessThanSuc_atLeastAtMost distrib_left order_refl sum.atLeast0_lessThan_Suc)
    also have "... \<le> (\<B> - 1) * (\<Sum>i=0..<n \<nu>. \<B>^i) + (b - 1) * \<B>^(n \<nu>)"
      by (smt (verit, ccfv_SIG) b_le_\<B> \<B>_power2 is_power2_ge1 mult_right_mono sum_nonneg 
          zero_le_power)
    also have "... = \<B>^(n \<nu>) - 1 + (b - 1) * \<B>^(n \<nu>)"
      by (simp add: \<B>_ge_2 atLeast0LessThan power_diff_1_eq)
    also have "... = b * \<B>^(n \<nu>) - 1"
      by (simp add: algebra_simps)
    also have "... < b * \<B>^(n \<nu>)"
      by auto
    finally show ?thesis .
  qed

  have tau_KB: "\<tau> (nat (2 * K g)) (nat ((\<B> - 2) * \<B>^(n (\<nu>+1)))) = 0"
  proof -
    have "insertion (y(0 := a)) P = 0"
      using assm unfolding statement1_strong_def statement1_weak_def by auto
    thus ?thesis 
      using lemma_1_8_helper(1) g_def y_bound by auto
  qed

  have tau_gM: "\<tau> (nat g) (nat (M)) = 0"
  proof -
    define C where "C \<equiv> b * \<B>^(n \<nu>)"

  interpret masking: masking_lemma \<delta> \<nu> "(nat \<B>)" "(nat b)" "(nat C)"
    unfolding masking_lemma_def C_def n_def using \<delta>_pos \<B>_power2 b_power2 \<B>_ge_2 b_le_\<B> is_power2_ge1
    by (smt (verit, ccfv_SIG) \<B>_even dvd_imp_le even_nat_iff mult_le_mono1 nat_eq_iff2 
      nat_less_eq_zless nat_mult_distrib nat_power_eq order_le_less zero_less_nat_eq)

  have 1: "nat g = (\<Sum>i=1..\<nu>. nat (y i) * (nat \<B>)^(n i))"
    proof -
      have "0 \<le> y i * \<B>^(n i)" for i
        using y_bound is_power2_ge1[OF \<B>_power2] by auto
      hence "nat g = (\<Sum>i=1..\<nu>. nat (y i * \<B>^(n i)))"
        unfolding g_def using nat_sum_distrib by auto
      also have "... = (\<Sum>i=1..\<nu>. nat (y i) * (nat \<B>)^(n i))"
        using y_bound is_power2_ge1[OF \<B>_power2] nat_mult_distrib nat_power_eq by auto
      finally show ?thesis .
    qed
    
    show ?thesis
    using masking.masking_lemma 1 y_bound 
    unfolding n_masking_lemma[OF masking.masking_lemma_axioms] 
              M_masking_lemma[OF masking.masking_lemma_axioms]
      by (meson nat_less_eq_zless)
  qed

  have tau_ST: "\<tau> (nat (S g)) (nat (T)) = 0"
    using tau_S_T_decomp g_lower_bound g_upper_bound is_power2_ge1[OF b_power2] tau_KB tau_gM 
    by auto
  
  have dvd_XY: "Y dvd (2 * nat (X g) choose nat (X g))"
  proof -
    have 0: "0 \<le> T \<and> T < N"
      using T_bound g_lower_bound g_upper_bound is_power2_ge1[OF b_power2] by force
    have 1: "0 \<le> S g \<and> S g < N"
      using S_bound g_lower_bound g_upper_bound is_power2_ge1[OF b_power2] by force
    have 2: "Tau_Reduction (nat (N)) (nat (S g)) (nat (T))"
      unfolding Tau_Reduction_def using N_power2 0 1
      by (metis int_one_le_iff_zero_less is_power2_ge1 nat_0_le order_le_less zless_nat_conj)
    have 3: "Tau_Reduction.R (nat (N)) (nat (S g)) (nat (T)) = nat (R g)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = nat ((S g + T + 1) * N + T + 1)"
        unfolding Tau_Reduction.R_def[OF 2] using 0 1 by (simp add: nat_add_distrib nat_mult_distrib)
      also have "... = nat (R g)" 
        unfolding R_def by simp
      finally show ?thesis unfolding Tau_Reduction.R_def[OF 2] by simp
    qed
   
    have "(nat N)^2 dvd (2 * (nat N - 1) * (nat (R g)) choose (nat N - 1) * nat (R g))"
      using Tau_Reduction.tau_as_binomial_coefficient[OF 2] 3 tau_ST by presburger
    hence "nat ((N)^2) dvd (2 * nat ((N - 1) * R g) choose nat ((N - 1) * R g))"
      using is_power2_ge1[OF N_power2]
      by (simp add: ab_semigroup_mult_class.mult_ac(1) nat_diff_distrib nat_mult_distrib nat_power_eq)
    hence "nat (Y) dvd (2 * nat (X g) choose nat (X g))"
      unfolding X_def Y_def by simp
    thus ?thesis 
      by auto
  qed 

  have "b * \<B>^(n \<nu>) = (int \<gamma>) * b^\<alpha>"
    unfolding \<B>_def \<alpha>_def \<gamma>_def by (simp add: power_mult power_mult_distrib)
  thus "statement2_strong g" 
    unfolding statement2_strong_def using g_lower_bound g_upper_bound dvd_XY by auto
qed

lemma coding_theorem_reverse:
  "statement2_weak g \<Longrightarrow> (\<exists>y. statement1_weak y)"
proof -
  assume assm: "statement2_weak g"
  
  have g_bound: "0 \<le> g \<and> g < 2 * b * \<B>^(n \<nu>)"
  proof -
    have "b * \<B>^(n \<nu>) = (int \<gamma>) * b^\<alpha>"
      unfolding \<B>_def \<gamma>_def \<alpha>_def by (simp add: power_mult power_mult_distrib)
    thus ?thesis
      using assm unfolding statement2_weak_def by auto
  qed

  have tau_ST: "\<tau> (nat (S g)) (nat (T)) = 0"
  proof -
    have 0: "0 \<le> T \<and> T < N"
      using T_bound g_bound is_power2_ge1[OF b_power2] by force
    have 1: "0 \<le> S g \<and> S g < N"
      using S_bound g_bound is_power2_ge1[OF b_power2] by force
    have 2: "Tau_Reduction (nat (N)) (nat (S g)) (nat (T))"
      unfolding Tau_Reduction_def using N_power2 0 1
      by (metis int_one_le_iff_zero_less is_power2_ge1 nat_0_le order_le_less zless_nat_conj)
    have 3: "Tau_Reduction.R (nat (N)) (nat (S g)) (nat (T)) = nat (R g)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = nat ((S g + T + 1) * N + T + 1)"
        unfolding Tau_Reduction.R_def[OF 2] using 0 1 by (simp add: nat_add_distrib nat_mult_distrib)
      also have "... = nat (R g)" 
        unfolding R_def by simp
      finally show ?thesis .
    qed

    have "nat Y = (nat N)\<^sup>2"
      unfolding Y_def using is_power2_ge1[OF N_power2] by (simp add: nat_power_eq)
    moreover have "2 * nat (X g) = 2 * (nat N - 1) * nat (R g)"
      unfolding X_def using is_power2_ge1[OF N_power2]
      by simp (smt (verit, best) nat_1 nat_diff_distrib nat_mult_distrib)
    moreover have "nat (X g) = (nat N - 1) * nat (R g)"
      unfolding X_def using is_power2_ge1[OF N_power2]
      by simp (smt (verit, best) nat_1 nat_diff_distrib nat_mult_distrib)
    ultimately show ?thesis
      using Tau_Reduction.tau_as_binomial_coefficient[OF 2] 3 assm unfolding statement2_weak_def
      by (metis "0" bot_nat_0.extremum_strict nat_dvd_iff nat_eq_iff2
                nat_less_eq_zless zero_eq_power2)
  qed
   
  have tau_gM: "\<tau> (nat g) (nat (M)) = 0" 
   and tau_KB: "\<tau> (nat (2 * K g)) (nat ((\<B> - 2) * \<B>^(n (\<nu>+1)))) = 0"
    using tau_S_T_decomp g_bound tau_ST by simp_all

  define C :: int where "C \<equiv> \<B> * \<B>^(n \<nu>)"

  interpret masking: masking_lemma \<delta> \<nu> "(nat \<B>)" "(nat b)" "(nat C)"
  unfolding masking_lemma_def C_def n_def using \<delta>_pos \<B>_power2 b_power2 \<B>_ge_2 b_le_\<B> is_power2_ge1
  by (smt (verit, ccfv_SIG) \<B>_even dvd_imp_le even_nat_iff mult_le_mono1 nat_eq_iff2 
      nat_less_eq_zless nat_mult_distrib nat_power_eq order_le_less zero_less_nat_eq)

  have 1: "nat g < nat C"
    unfolding C_def using g_bound N0_def g_lt_N0 n_def by force    

  obtain y::"nat\<Rightarrow>nat" 
    where g_sum_y: "nat g = (\<Sum>i=1..\<nu>. y i * (nat \<B>)^(n i))"
      and y_bound: "\<forall>i. y i < nat b"
      using masking.masking_lemma 1 tau_gM 
      unfolding n_masking_lemma[OF masking.masking_lemma_axioms] M_masking_lemma[OF masking.masking_lemma_axioms]
      by blast
  
  define z::"nat\<Rightarrow>int" where "z \<equiv> (\<lambda>i. if i = 0 then a else int (y i))"
    
  have g_sum: "g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))"
  proof -
    have "i\<in>{1..\<nu>} \<Longrightarrow> z i * \<B>^(n i) = int (y i * (nat \<B>)^(n i))" for i
      using \<B>_ge_2 z_def by auto
    hence "(\<Sum>i=1..\<nu>. z i * \<B>^(n i)) = (\<Sum>i=1..\<nu>. int (y i * (nat \<B>)^(n i)))"
      by simp
    also have "... = int (\<Sum>i=1..\<nu>. y i * (nat \<B>)^(n i))"
      by simp
    also have "... = int (nat g)" 
      using g_sum_y by simp
    also have "... = g" 
      using g_bound by auto
    finally show ?thesis 
      by auto
  qed

  have z_bound: "0 \<le> z i \<and> z i < b" for i   
  proof (cases "i = 0")
    case True thus ?thesis 
      unfolding z_def b_def using a_nonneg f_pos
      by simp (smt (verit, ccfv_SIG) mult_less_cancel_left2)
  next
    case False thus ?thesis
      unfolding z_def apply simp using y_bound zless_nat_eq_int_zless by blast
  qed

  have z_0: "z 0 = a"
    unfolding z_def by simp
 
  have "insertion z P = 0"
    using lemma_1_8_helper(1)[OF g_sum] z_bound tau_KB z_0 by auto
  thus ?thesis
    unfolding statement1_weak_def using z_bound z_0 by auto
qed

lemma coding_theorem_reverse':
  assumes "\<exists>g. 0 \<le> g \<and> g < 2 * (int \<gamma>) * b^\<alpha> \<and> Y dvd (2 * nat (X g) choose nat (X g))"
  shows "\<exists>z. (z 0 = a) \<and> (\<forall>i. 0 \<le> z i \<and> z i < b) \<and> insertion z P = 0"
  using coding_theorem_reverse[unfolded statement2_weak_def statement1_weak_def]
  using assms by auto

end

end