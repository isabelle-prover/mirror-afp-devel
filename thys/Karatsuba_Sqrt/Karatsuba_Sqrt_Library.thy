subsection \<open>Auxiliary material\<close>
theory Karatsuba_Sqrt_Library
imports
  Complex_Main
  "HOL-Library.Discrete"
  "HOL-Library.Log_Nat"
begin

subsection \<open>Efficient simultaneous computation of \<open>div\<close> and \<open>mod\<close>\<close>

definition divmod_int :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "divmod_int a b = (a div b, a mod b)"

lemma divmod_int_code [code]:
  "divmod_int a b =
     (case divmod_integer (integer_of_int a) (integer_of_int b) of
       (q, r) \<Rightarrow> (int_of_integer q, int_of_integer r))"
  by (simp add: divmod_int_def divmod_integer_def)


subsubsection \<open>Missing lemmas about \<^const>\<open>bitlen\<close>\<close>

lemma drop_bit_eq_0_iff_nat:
  "drop_bit k (n :: nat) = 0 \<longleftrightarrow> bitlen n \<le> k"
  by (auto simp: drop_bit_eq_div div_eq_0_iff less_power_nat_iff_bitlen)

lemma drop_bit_eq_0_iff_int:
  assumes "n \<ge> 0"
  shows   "drop_bit k (n :: int) = 0 \<longleftrightarrow> bitlen n \<le> k"
  by (metis assms drop_bit_eq_0_iff_nat drop_bit_nat_eq drop_bit_of_nat nat_0_le nat_zero_as_int of_nat_0)

lemma drop_bit_bitlen_minus_1: 
  assumes "n > 0"
  shows   "drop_bit (nat (bitlen n - 1)) n = 1"
proof -
  define s where "s = nat (bitlen n - 1)"
  have "bitlen n > 0"
    using assms by (simp add: bitlen_eq_zero_iff bitlen_nonneg order_less_le)
  have "drop_bit s n \<le> drop_bit s (mask (s+1))"
    unfolding drop_bit_eq_div mask_eq_exp_minus_1
    using \<open>bitlen n > 0\<close> bitlen_bounds[of n] assms
    by (intro zdiv_mono1)
       (auto simp: s_def nat_diff_distrib simp del: power_Suc)
  also have "drop_bit s (mask (s + 1) :: int) = 1"
    by (simp add: drop_bit_mask_eq)
  finally have "drop_bit s n \<le> 1" .
  moreover have "drop_bit s n \<noteq> 0"
    using assms \<open>bitlen n > 0\<close>
    by (subst drop_bit_eq_0_iff_int) (auto simp: s_def)
  moreover have "drop_bit s n \<ge> 0"
    using assms by auto
  ultimately show "drop_bit s n = 1"
    by linarith
qed

lemma bitlen_pos: "n > 0 \<Longrightarrow> bitlen n > 0"
  using bitlen_def bitlen_eq_zero_iff linorder_not_less by auto

lemma bit_bitlen_minus_1: 
  assumes "n > 0"
  shows   "bit n (nat (bitlen n - 1))"
  using drop_bit_bitlen_minus_1[OF assms]
  by (simp add: bit_iff_and_drop_bit_eq_1)

lemma not_bit_ge_bitlen:
  assumes "int k \<ge> bitlen n" "n \<ge> 0"
  shows   "\<not>bit n k"
proof
  assume "bit n k"
  hence "odd (n div 2 ^ k)"
    by (auto simp: bit_iff_odd)
  hence "n \<ge> 2 ^ k"
    using assms(2) linorder_not_le by fastforce 
  hence "int k < bitlen n"
    by (metis bitlen_le_iff_power linorder_not_less nat_int)
  thus False
    using assms by auto
qed

lemma bitlen_eqI:
  assumes "bit n (nat k - 1)" "\<And>i. int i \<ge> k \<Longrightarrow> \<not>bit n i" "k > 0" "n \<ge> 0"
  shows   "bitlen n = k"
proof -
  from assms(1) have "n \<noteq> 0"
    by auto
  with \<open>n \<ge> 0\<close> have "n > 0"
    by auto
  show ?thesis
  proof (cases "bitlen n" k rule: linorder_cases)
    assume "bitlen n > k"
    hence False
      using assms(2)[of "nat (bitlen n - 1)"] bit_bitlen_minus_1[of n] \<open>n > 0\<close>
      by (auto split: if_splits simp: bitlen_pos)
    thus ?thesis ..
  next
    assume "bitlen n < k"
    hence False
      using assms(1) \<open>k > 0\<close> not_bit_ge_bitlen[of n "nat k - 1"] \<open>n > 0\<close>
      by (auto simp: of_nat_diff)
    thus ?thesis ..
  qed auto
qed

lemma bitlen_drop_bit:
  assumes "n \<ge> 0"
  shows   "bitlen (drop_bit k n) = max 0 (bitlen n - k)"
proof (cases "bitlen n > k")
  case False
  hence "drop_bit k n = 0"
    using assms by (subst drop_bit_eq_0_iff_int) auto
  thus ?thesis using False
    by simp
next
  case True
  hence "n \<noteq> 0"
    by auto
  with assms have "n > 0"
    by auto
  show ?thesis
  proof (rule bitlen_eqI)
    show "bit (drop_bit k n) (nat (max 0 (bitlen n - int k)) - 1)"
      using True bit_bitlen_minus_1[of n] \<open>n > 0\<close>
      by (auto simp: bit_drop_bit_eq nat_diff_distrib)
  next
    fix i :: nat
    assume "max 0 (bitlen n - int k) \<le> int i"
    hence "int (i + k) \<ge> bitlen n"
      using True by simp
    thus "\<not> bit (drop_bit k n) i"
      using \<open>n > 0\<close> by (auto simp: bit_drop_bit_eq not_bit_ge_bitlen)
  qed (use True \<open>n > 0\<close> in auto)
qed


subsubsection \<open>Missing lemmas about \<^const>\<open>Discrete.sqrt\<close>\<close>

lemma Discrete_sqrt_lessI:
  assumes "x < y ^ 2"
  shows   "Discrete.sqrt x < y"
  using assms Discrete.le_sqrt_iff linorder_not_less by blast

lemma Discrete_sqrt_conv_floor_sqrt:
  "Discrete.sqrt n = nat (floor (sqrt n))"
proof (rule Discrete.sqrt_unique)
  have "real (nat (floor (sqrt n)) ^ 2) = real_of_int \<lfloor>sqrt (real n)\<rfloor> ^ 2"
    by simp
  also have "\<dots> \<le> sqrt (real n) ^ 2"
    by (intro power_mono) auto
  also have "\<dots> = real n"
    by simp
  finally show "nat (floor (sqrt n)) ^ 2 \<le> n"
    by linarith
next
  have "sqrt (real n) ^ 2 < (real_of_int \<lfloor>sqrt (real n)\<rfloor> + 1) ^ 2"
    by (rule power_strict_mono) auto
  hence "real n < (real_of_int \<lfloor>sqrt (real n)\<rfloor> + 1) ^ 2"
    by simp
  also have "\<dots> = real ((Suc (nat (floor (sqrt n)))) ^ 2)"
    by simp
  finally show "n < Suc (nat (floor (sqrt n))) ^ 2"
    by linarith
qed


subsection \<open>Miscellaneous\<close>

lemma Let_cong:
  assumes "a = c" "\<And>x. x = a \<Longrightarrow> b x = d x"
  shows   "Let a b = Let c d"
  unfolding Let_def using assms by simp

lemma case_prod_cong:
  assumes "a = b" "\<And>x y. a = (x, y) \<Longrightarrow> f x y = g x y"
  shows   "(case a of (x, y) \<Rightarrow> f x y) = (case b of (x, y) \<Rightarrow> g x y)"
  using assms by (auto simp: case_prod_unfold)

end