(*
  File:     Continued_Fractions/Pell_Continued_Fraction.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>The Connection between the continued fraction expansion of square roots and Pell's equation\<close>
theory Pell_Continued_Fraction
imports
  Sqrt_Nat_Cfrac
  Pell.Pell_Algorithm
  Polynomial_Factorization.Prime_Factorization  
  Pell_Lifting
begin

lemma irrational_times_int_eq_intD:
  assumes "p * real_of_int a = real_of_int b"
  assumes "p \<notin> \<rat>"
  shows   "a = 0 \<and> b = 0"
proof -
  have "a = 0"
  proof (rule ccontr)
    assume "a \<noteq> 0"
    with assms(1) have "p = b / a" by (auto simp: field_simps)
    also have "\<dots> \<in> \<rat>" by auto
    finally show False using assms(2) by contradiction
  qed
  with assms show ?thesis by simp
qed


text \<open>
  The solutions to Pell's equation for some non-square \<open>D\<close> are linked to the continued
  fraction expansion of $\sqrt{D}$, which we shall show here.  
\<close>

context
  fixes D :: nat and c h k P Q l
  assumes nonsquare: "\<not>is_square D"
  defines "c \<equiv> cfrac_of_real (sqrt D)"
  defines "h \<equiv> conv_num c" and "k \<equiv> conv_denom c"
  defines "P \<equiv> fst \<circ> sqrt_remainder_surd D" and "Q \<equiv> snd \<circ> sqrt_remainder_surd D"
  defines "l \<equiv> sqrt_nat_period_length D"
begin

interpretation pell D
  by unfold_locales fact+

lemma cfrac_length_infinite [simp]: "cfrac_length c = \<infinity>"
proof -
  have "sqrt D \<notin> \<rat>"
    using nonsquare by (simp add: irrat_sqrt_nonsquare)
  thus ?thesis
    by (simp add: c_def)
qed

lemma conv_num_denom_pell:
  "h 0 ^ 2 - D * k 0 ^ 2 < 0"
  "m > 0 \<Longrightarrow> h m ^ 2 - D * k m ^ 2 = (-1) ^ Suc m * Q m"
proof -
  define D' where "D' = Discrete.sqrt D"
  have "h 0 ^ 2 - D * k 0 ^ 2 = int (D' ^ 2) - int D"
    by (simp_all add: h_def k_def c_def Discrete_sqrt_altdef D'_def)
  also {
    have "int (D' ^ 2) - int D \<le> 0"
      using Discrete.sqrt_power2_le[of D] by (simp add: D'_def)
    moreover have "D \<noteq> D' ^ 2" using nonsquare by auto
    ultimately have "int (D' ^ 2) - int D < 0" by linarith
  }
  finally show "h 0 ^ 2 - D * k 0 ^ 2 < 0" .
next
  assume "m > 0"
  define n where "n = m - 1"
  define \<alpha> where "\<alpha> = cfrac_remainder c"
  define \<alpha>' where "\<alpha>' = sqrt_remainder_surd D"
  have m: "m = Suc n" using \<open>m > 0\<close> by (simp add: n_def)
  from nonsquare have "D > 1"
    by (cases D) (auto intro!: Nat.gr0I)
  from nonsquare have irrat: "sqrt D \<notin> \<rat>"
    using irrat_sqrt_nonsquare by blast
  have [simp]: "cfrac_lim c = sqrt D"
    using irrat \<open>D > 1\<close> by (simp add: c_def)
  have \<alpha>_pos: "\<alpha> n > 0" for n
    unfolding \<alpha>_def using wf \<open>D > 1\<close> cfrac_remainder_pos[of c n]
    by (cases "n = 0") auto
  have \<alpha>': "\<alpha>' n = (P n, Q n)" for n by (simp add: \<alpha>'_def P_def Q_def)
  have Q_pos: "Q n > 0" for n
    using snd_sqrt_remainder_surd_pos[OF nonsquare] by (simp add: Q_def)
  have k_pos: "k n > 0" for n
    by (auto simp: k_def intro!: conv_denom_pos)
  have k_nonneg: "k n \<ge> 0" for n
    by (auto simp: k_def intro!: conv_denom_nonneg)

  let ?A = "(sqrt D + P (n + 1)) * h (n + 1) + Q (n + 1) * h n"
  let ?B = "(sqrt D + P (n + 1)) * k (n + 1) + Q (n + 1) * k n"
  have "?B > 0" using k_pos Q_pos k_nonneg
    by (intro add_nonneg_pos mult_nonneg_nonneg add_nonneg_nonneg) auto
  
  have "sqrt D = conv' c (Suc (Suc n)) (\<alpha> (Suc (Suc n)))"
    unfolding \<alpha>_def by (subst conv'_cfrac_remainder) auto
  also have "\<dots> = (\<alpha> (n + 2) * h (n + 1) + h n) / (\<alpha> (n + 2) * k (n + 1) + k n)"
    using wf \<alpha>_pos by (subst conv'_num_denom) (simp_all add: h_def k_def)
  also have "\<alpha> (n + 2) = surd_to_real D (\<alpha>' (Suc n))"
    using surd_to_real_sqrt_remainder_surd[OF nonsquare, of "Suc n"]
    by (simp add: \<alpha>'_def \<alpha>_def c_def)
  also have "\<dots> = (sqrt D + P (Suc n)) / Q (Suc n)" (is "_ = ?\<alpha>")
    by (simp add: \<alpha>' surd_to_real_def)
  also have "?\<alpha> * h (n + 1) + h n =
               1 / Q (n + 1) * ((sqrt D + P (n + 1)) * h (n + 1) + Q (n + 1) * h n)"
    using Q_pos by (simp add: field_simps)
  also have "?\<alpha> * k (n + 1) + k n =
               1 / Q (n + 1) * ((sqrt D + P (n + 1)) * k (n + 1) + Q (n + 1) * k n)"
    (is "_ = ?f k") using Q_pos by (simp add: field_simps)
  also have "?f h / ?f k = ((sqrt D + P (n + 1)) * h (n + 1) + Q (n + 1) * h n) /
                             ((sqrt D + P (n + 1)) * k (n + 1) + Q (n + 1) * k n)"
    (is "_ = ?A / ?B") using Q_pos by (intro mult_divide_mult_cancel_left) auto
  finally have "sqrt D * ?B = ?A"
    using \<open>?B > 0\<close> by (simp add: divide_simps)
  moreover have "sqrt D * sqrt D = D" by simp
  ultimately have "sqrt D * (P (n + 1) * k (n + 1) + Q (n + 1) * k n - h (n + 1)) =
         P (n + 1) * h (n + 1) + Q (n + 1) * h n - k (n + 1) * D"
    unfolding of_int_add of_int_mult of_int_diff of_int_of_nat_eq of_nat_mult of_nat_add
    by Groebner_Basis.algebra
  from irrational_times_int_eq_intD[OF this] irrat
    have 1: "h (Suc n) = P (Suc n) * k (Suc n) + Q (Suc n) * k n"
     and 2: "D * k (Suc n) = P (Suc n) * h (Suc n) + Q (Suc n) * h n"
      by (simp_all del: of_nat_add of_nat_mult)

  have "h (Suc n) * h (Suc n) - D * k (Suc n) * k (Suc n) =
          Q (Suc n) * (k n * h (Suc n) - k (Suc n) * h n)"
    by (subst 1, subst 2) (simp add: algebra_simps)
  also have "k n * h (Suc n) - k (Suc n) * h n = (-1) ^ n"
    unfolding h_def k_def by (rule conv_num_denom_prod_diff)
  finally have "h (Suc n) ^ 2 - D * k (Suc n) ^ 2 = (-1) ^ n * Q (Suc n)"
    by (simp add: power2_eq_square algebra_simps)
  thus "h m ^ 2 - D * k m ^ 2 = (-1) ^ Suc m * Q m"
    by (simp add: m)
qed

text \<open>
  Every non-trivial solution to Pell's equation is a convergent in the expansion of $\sqrt{D}$:
\<close>
theorem pell_solution_is_conv:
  assumes "x\<^sup>2 = Suc (D * y\<^sup>2)" and "y > 0"
  shows   "(int x, int y) \<in> range (\<lambda>n. (conv_num c n, conv_denom c n))"
proof -
  have "\<exists>n. enat n \<le> cfrac_length c \<and> (int x, int y) = (conv_num c n, conv_denom c n)"
  proof (rule frac_is_convergentI)
    have "gcd (x\<^sup>2) (y\<^sup>2) = 1" unfolding assms(1)
      using gcd_add_mult[of "y\<^sup>2" D 1] by (simp add: gcd.commute)
    thus "coprime (int x) (int y)"
      by (simp add: coprime_iff_gcd_eq_1)
  next
    from assms have "D > 1"
      using nonsquare by (cases D) (auto intro!: Nat.gr0I)
    hence pos: "x + y * sqrt D > 0" using assms
      by (intro add_nonneg_pos) auto
  
    from assms have "real (x\<^sup>2) = real (Suc (D * y\<^sup>2))"
      by (simp only: of_nat_eq_iff)
    hence "1 = real x ^ 2 - D * real y ^ 2"
      unfolding of_nat_power by simp
    also have "\<dots> = (x - y * sqrt D) * (x + y * sqrt D)"
      by (simp add: field_simps power2_eq_square)
    finally have *: "x - y * sqrt D = 1 / (x + y * sqrt D)"
      using pos by (simp add: field_simps)
  
    from pos have "0 < 1 / (x + y * sqrt D)"
      by (intro divide_pos_pos) auto
    also have "\<dots> = x - y * sqrt D" by (rule * [symmetric])
    finally have less: "y * sqrt D < x" by simp
  
    have "sqrt D - x / y = -((x - y * sqrt D) / y)"
      using \<open>y > 0\<close> by (simp add: field_simps)
    also have "\<bar>\<dots>\<bar> = (x - y * sqrt D) / y"
      using less by simp
    also have "(x - y * sqrt D) / y = 1 / (y * (x + y * sqrt D))"
      using \<open>y > 0\<close> by (subst *) auto
    also have "\<dots> \<le> 1 / (y * (y * sqrt D + y * sqrt D))"
      using \<open>y > 0\<close> \<open>D > 1\<close> pos less
      by (intro divide_left_mono mult_left_mono add_right_mono mult_pos_pos) auto
    also have "\<dots> = 1 / (2 * y\<^sup>2 * sqrt D)"
      by (simp add: power2_eq_square)
    also have "\<dots> < 1 / (real (2 * y\<^sup>2) * 1)" using \<open>y > 0\<close> \<open>D > 1\<close>
      by (intro divide_strict_left_mono mult_strict_left_mono mult_pos_pos) auto
    finally show "\<bar>cfrac_lim c - int x / int y\<bar> < 1 / (2 * int y ^ 2)"
      unfolding c_def using irrat_sqrt_nonsquare[of D] \<open>\<not>is_square D\<close> by simp
  qed (insert assms irrat_sqrt_nonsquare[of D], auto simp: c_def)
  thus ?thesis by auto
qed

text \<open>
  Let \<open>l\<close> be the length of the period in the continued fraction expansion of $\sqrt{D}$ and let
  $h_i$ and $k_i$ be the numerator and denominator of the \<open>i\<close>-th convergent.

  Then the non-trivial solutions of Pell's equation are exactly the pairs of the form
  $(h_{lm -1}, k_{lm-1})$ for any \<open>m\<close> such that $lm$ is even.
\<close>
lemma nontriv_solution_iff_conv_num_denom:
  "nontriv_solution (x, y) \<longleftrightarrow>
     (\<exists>m>0. int x = h (l * m - 1) \<and> int y = k (l * m - 1) \<and> even (l * m))"
proof safe
  fix m assume xy: "x = h (l * m - 1)" "y = k (l * m - 1)" 
           and lm: "even (l * m)" and m: "m > 0"
  have l: "l > 0" using period_nonempty[OF nonsquare] by (auto simp: l_def)
  from lm have "l * m \<noteq> 1" by (intro notI) auto
  with l m have lm': "l * m > 1" by (cases "l * m") auto

  have "(h (l * m - 1))\<^sup>2 - D * (k (l * m - 1))\<^sup>2 =
          (- 1) ^ Suc (l * m - 1) * int (Q (l * m - 1))"
    using lm' by (intro conv_num_denom_pell) auto
  also have "(- 1) ^ Suc (l * m - 1) = (1 :: int)"
    using lm l m by (subst neg_one_even_power) auto
  also have "Q (l * m - 1) = Q ((l * m - 1) mod l)"
    unfolding Q_def l_def o_def by (subst sqrt_remainder_surd_periodic[OF nonsquare]) simp
  also {
    have "l * m - 1 = (m - 1) * l + (l - 1)"
      using m l lm' by (cases m) (auto simp: mult_ac)
    also have "\<dots> mod l = (l - 1) mod l"
      by simp
    also have "\<dots> = l - 1"
      using l by (intro mod_less) auto
    also have "Q \<dots> = 1"
      using sqrt_remainder_surd_last[OF nonsquare] by (simp add: Q_def l_def)
    finally have "Q ((l * m - 1) mod l) = 1" .
  }
  finally have "h (l * m - 1) ^ 2 =  D * k (l * m - 1) ^ 2 + 1"
    unfolding of_nat_Suc by (simp add: algebra_simps)
  hence "h (l * m - 1) ^ 2 = D * k (l * m - 1) ^ 2 + 1"
    by (simp only: of_nat_eq_iff)
  moreover have "k (l * m - 1) > 0"
    unfolding k_def by (intro conv_denom_pos)
  ultimately have "nontriv_solution (int x, int y)"
    using xy by (simp add: nontriv_solution_def)
  thus "nontriv_solution (x, y)"
    by simp
next
  assume "nontriv_solution (x, y)"
  hence asm: "x ^ 2 = Suc (D * y ^ 2)" "y > 0"
    by (auto simp: nontriv_solution_def abs_square_eq_1 intro!: Nat.gr0I)
  from asm have asm': "int x ^ 2 = int D * int y ^ 2 + 1"
    by (metis add.commute of_nat_Suc of_nat_mult of_nat_power_eq_of_nat_cancel_iff)
  have l: "l > 0" using period_nonempty[OF nonsquare] by (auto simp: l_def)
  from pell_solution_is_conv[OF asm] obtain m where
    xy: "h m = x" "k m = y" by (auto simp: c_def h_def k_def)

  have m: "m > 0"
    using asm' conv_num_denom_pell(1) xy by (intro Nat.gr0I) auto
  have "1 = h m ^ 2 - D * k m ^ 2"
    using asm' xy by simp
  also have "\<dots> = (- 1) ^ Suc m * int (Q m)"
    using conv_num_denom_pell(2)[OF m] .
  finally have *: "(- 1) ^ Suc m * int (Q m) = 1" ..
  from * have m': "odd m \<and> Q m = 1"
    by (cases "even m") auto

  define n where "n = Suc m div l"
  have "l dvd Suc m"
  proof (rule ccontr)
    assume *: "\<not>(l dvd Suc m)"
    have "Q m = Q (m mod l)"
      unfolding Q_def l_def o_def by (subst sqrt_remainder_surd_periodic[OF nonsquare]) simp  
    also {
      have "m mod l < l" using \<open>l > 0\<close> by simp
      moreover have "Suc (m mod l) \<noteq> l" using * l \<open>m > 0\<close>
        using mod_Suc[of m l] by auto
      ultimately have "m mod l < l - 1" by simp
      hence "Q (m mod l) > 1" unfolding Q_def o_def l_def
        by (rule snd_sqrt_remainder_surd_gt_1[OF nonsquare])
    }
    finally show False using m' by simp
  qed
  hence m_eq: "Suc m = n * l" "m = n * l - 1"
    by (simp_all add: n_def)
  hence "n > 0" by (auto intro!: Nat.gr0I)
  thus "\<exists>n>0. int x = h (l * n - 1) \<and> int y = k (l * n - 1) \<and> even (l * n)"
    using xy m_eq m' by (intro exI[of _ n]) (auto simp: mult_ac)
qed  

text \<open>
  Consequently, the fundamental solution is $(h_n, k_n)$ where $n = l - 1$
  if \<open>l\<close> is even and $n = 2l-1$ otherwise:
\<close>
lemma fund_sol_conv_num_denom:
  defines "n \<equiv> if even l then l - 1 else 2 * l - 1"
  shows   "fund_sol = (nat (h n), nat (k n))"
proof (rule fund_sol_eq_sndI)
  have [simp]: "h n \<ge> 0" "k n \<ge> 0" for n
    by (auto simp: h_def k_def c_def intro!: conv_num_nonneg)
  show "nontriv_solution (nat (h n), nat (k n))"
    by (subst nontriv_solution_iff_conv_num_denom, rule exI[of _ "if even l then 1 else 2"])
       (simp_all add: n_def mult_ac)
next
  fix x y :: nat assume "nontriv_solution (x, y)"
  then obtain m where m: "m > 0" "x = h (l * m - 1)" "y = k (l * m - 1)" "even (l * m)"
    by (subst (asm) nontriv_solution_iff_conv_num_denom) auto
  have l: "l > 0" using period_nonempty[OF nonsquare] by (auto simp: l_def)
  from m l have "Suc n \<le> l * m" by (auto simp: n_def)
  hence "n \<le> l * m - 1" by simp
  hence "k n \<le> k (l * m - 1)"
    unfolding k_def c_def using irrat_sqrt_nonsquare[OF nonsquare]
    by (intro conv_denom_leI) auto
  with m show "nat (k n) \<le> y" by simp
qed

end


text \<open>
  The following algorithm computes the fundamental solution (or the dummy result \<open>(0, 0)\<close> if
  \<open>D\<close> is a square) fairly quickly by computing the continued fraction expansion of $\sqrt{D}$
  and then computing the fundamental solution as the appropriate convergent.
\<close>
lemma find_fund_sol_code [code]:
  "find_fund_sol D =
     (let info = sqrt_cfrac_info_array D;
          l = fst info
      in  if l = 0 then (0, 0) else
            let
              c = cfrac_sqrt_nth info;
              n = if even l then l - 1 else 2 * l - 1
          in
            (nat (conv_num_fun c n), nat (conv_denom_fun c n)))"
proof -
  have *: "is_cfrac (cfrac_sqrt_nth (sqrt_cfrac_info_array D))" if "\<not>is_square D"
    using that cfrac_sqrt_nth[of D] unfolding is_cfrac_def
    by (metis cfrac_nth_nonzero neq0_conv of_nat_0 of_nat_0_less_iff)
  have **: "cfrac (\<lambda>x. int (cfrac_sqrt_nth (sqrt_cfrac_info_array D) x)) = cfrac_of_real (sqrt D)"
    if "\<not>is_square D"
    using that cfrac_sqrt_nth[of D] * by (intro cfrac_eqI) auto
  show ?thesis using * **
    by (auto simp: square_test_correct find_fund_sol_correct conv_num_fun_eq conv_denom_fun_eq
                   Let_def cfrac_sqrt_nth fund_sol_conv_num_denom conv_num_nonneg)
qed

lemma find_nth_solution_square [simp]: "is_square D \<Longrightarrow> find_nth_solution D n = (0, 0)"
  by (simp add: find_nth_solution_def)

lemma fst_find_fund_sol_eq_0_iff [simp]: "fst (find_fund_sol D) = 0 \<longleftrightarrow> is_square D"
proof (cases "is_square D")
  case False
  then interpret pell D by unfold_locales
  from False have "find_fund_sol D = fund_sol" by (simp add: find_fund_sol_correct)
  moreover from fund_sol_is_nontriv_solution have "fst fund_sol > 0"
    by (auto simp: nontriv_solution_def intro!: Nat.gr0I)
  ultimately show ?thesis using False
    by (simp add: find_fund_sol_def square_test_correct split: if_splits)
qed (auto simp: find_fund_sol_def square_test_correct)

text \<open>
  Arbitrary solutions can now be computed as powers of the fundamental solution.
\<close>
lemma find_nth_solution_code [code]:
  "find_nth_solution D n =
     (let xy = find_fund_sol D
      in  if fst xy = 0 then (0, 0) else efficient_pell_power D xy n)"
proof (cases "is_square D")
  case False
  then interpret pell D by unfold_locales
  from fund_sol_is_nontriv_solution have "fst fund_sol > 0"
    by (auto simp: nontriv_solution_def intro!: Nat.gr0I)
  thus ?thesis using False
    by (simp add: find_nth_solution_correct Let_def nth_solution_def pell_power_def 
                  pell_mul_commutes[of _ "fund_sol"] find_fund_sol_correct)
qed auto

lemma nth_solution_code [code]:
  "pell.nth_solution D n = 
     (let info = sqrt_cfrac_info_array D;
          l = fst info
      in  if l = 0 then
             Code.abort (STR ''nth_solution is undefined for perfect square parameter.'')
               (\<lambda>_. pell.nth_solution D n)
          else
            let
              c = cfrac_sqrt_nth info;
              m = if even l then l - 1 else 2 * l - 1;
              fund_sol = (nat (conv_num_fun c m), nat (conv_denom_fun c m))
            in
              efficient_pell_power D fund_sol n)"
proof (cases "is_square D")
  case False
  then interpret pell by unfold_locales
  have *: "is_cfrac (cfrac_sqrt_nth (sqrt_cfrac_info_array D))"
    using False cfrac_sqrt_nth[of D] unfolding is_cfrac_def
    by (metis cfrac_nth_nonzero neq0_conv of_nat_0 of_nat_0_less_iff)
  have **: "cfrac (\<lambda>x. int (cfrac_sqrt_nth (sqrt_cfrac_info_array D) x)) = cfrac_of_real (sqrt D)"
    using False cfrac_sqrt_nth[of D] * by (intro cfrac_eqI) auto

  from False * ** show ?thesis
    by (auto simp: Let_def cfrac_sqrt_nth fund_sol_conv_num_denom nth_solution_def
                   pell_power_def pell_mul_commutes[of _ "(_, _)"]
                   conv_num_fun_eq conv_denom_fun_eq conv_num_nonneg)
qed auto

lemma fund_sol_code [code]:
  "pell.fund_sol D = (let info = sqrt_cfrac_info_array D;
          l = fst info
      in  if l = 0 then
             Code.abort (STR ''fund_sol is undefined for perfect square parameter.'')
               (\<lambda>_. pell.fund_sol D)
          else
            let
              c = cfrac_sqrt_nth info;
              n = if even l then l - 1 else 2 * l - 1
            in
              (nat (conv_num_fun c n), nat (conv_denom_fun c n)))"
proof (cases "is_square D")
  case False
  then interpret pell by unfold_locales
  have *: "is_cfrac (cfrac_sqrt_nth (sqrt_cfrac_info_array D))"
    using False cfrac_sqrt_nth[of D] unfolding is_cfrac_def
    by (metis cfrac_nth_nonzero neq0_conv of_nat_0 of_nat_0_less_iff)
  have **: "cfrac (\<lambda>x. int (cfrac_sqrt_nth (sqrt_cfrac_info_array D) x)) = cfrac_of_real (sqrt D)"
    using False cfrac_sqrt_nth[of D] * by (intro cfrac_eqI) auto

  from False * ** show ?thesis
    by (auto simp: Let_def cfrac_sqrt_nth fund_sol_conv_num_denom nth_solution_def
                   pell_power_def pell_mul_commutes[of _ "(_, _)"]
                   conv_num_fun_eq conv_denom_fun_eq conv_num_nonneg)
qed auto

end