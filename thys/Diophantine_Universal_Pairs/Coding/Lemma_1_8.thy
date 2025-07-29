theory Lemma_1_8                                 
  imports Lemma_1_8_Coding
begin

subsubsection \<open>Proof of the equivalence\<close>

locale Lemma_1_8 = K_Nonnegative +
  assumes \<B>_power2: "is_power2 (int \<B>)"
begin

lemma b_power2: "is_power2 (int b)" 
  using b_def int_ops is_power2_div2 \<B>_power2 \<B>_gt_2
  by (smt (verit) Suc_1 of_nat_less_iff)

(* K lower bound is shown previously in K_Nonnegative *)

lemma K_upper_bound: "K < int \<B>^((2*\<delta>+1) * n \<nu> + 1)"
proof -
  have "j \<in> {..(2*\<delta>+1) * n \<nu>} \<Longrightarrow> e j + b \<le> \<B> - 1" for j
    using e_b_bound \<B>_ge_1 by (simp add: of_nat_diff) 
  hence 0: "j \<in> {..(2*\<delta>+1) * n \<nu>} \<Longrightarrow> (e j + b) * \<B>^j \<le> (\<B> - 1) * \<B>^j" for j
    using \<B>_ge_1 by simp

  have 1: "(\<B> - 1) * (\<Sum>i\<le>n. \<B>^i) = \<B>^(n+1) - 1" for n
  proof (induction n)
    case 0 show ?case by simp
  next 
    case (Suc n)
    have "int ((\<B> - 1) * (\<Sum>i\<le>Suc n. \<B>^i)) = 
      int ((\<B> - 1) * (\<Sum>i\<le>n. \<B>^i) + (\<B> - 1) * \<B>^(Suc n))"
      by (auto simp add: algebra_simps)
    also have "... = int \<B>^(Suc n) - (1::int) + (\<B> - (1::int)) * int \<B>^(Suc n)"
      using int_ops Suc.IH \<B>_ge_1 by simp
    also have "... = int \<B> * \<B>^(Suc n) - 1"
      using int_ops by (simp add: algebra_simps)
    also have "... = int (\<B>^(Suc (Suc n)) - 1)"
      using \<B>_ge_1 int_ops by simp
    finally show ?case
      by (metis Suc_eq_plus1 of_nat_eq_iff)
  qed

  have "K \<le> (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (\<B> - 1) * int \<B>^i)"
    unfolding K_def using sum_mono 0
    by (metis (no_types, lifting) K_def K_expression of_nat_mult of_nat_power)
  also have "... = int ((\<B> - 1) * (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. \<B>^i))" 
    by (simp add: sum_distrib_left)
  also have "... = int (\<B>^((2*\<delta>+1) * n \<nu> + 1) - 1)"
    using 1 by simp
  also have "... = \<B>^((2*\<delta>+1) * n \<nu> + 1) - (1::int)"
    using \<B>_ge_1 int_ops(6) by auto
  also have "... < int \<B>^((2*\<delta>+1) * n \<nu> + 1)" by auto
  finally show ?thesis .
qed

lemma direct_implication: 
  "insertion z_assign P = 0 \<Longrightarrow> \<tau> (nat K) ((b-1) * \<B>^(n (\<nu>+1))) = 0"
proof -
  assume "insertion z_assign P = 0"
  hence assm: "e (n (\<nu>+1)) = 0" using e_n_\<nu>1_expression by simp
   
  define deg where "deg = (2*\<delta>+1) * n \<nu>"
  define x where "x = (\<lambda>i. nat (e i + int b))"
  define y where "y = (\<lambda>i. if i = n (\<nu>+1) then b-1 else 0)"

  have x_sum: "nat K = (\<Sum>i<deg+1. x i * \<B>^i)"
  proof -
    have 0: "(e i + int b) * \<B>^i \<ge> 0" for i
      using e_b_bound(1) by (simp add: dual_order.strict_implies_order)

    have "nat K = nat (\<Sum>i\<le>deg. (e i + int b) * \<B>^i)"
      unfolding K_expression deg_def by auto
    also have "... = (\<Sum>i\<le>deg. nat ((e i + int b) * \<B>^i))"
      using nat_sum_distrib 0 by auto
    also have "... = (\<Sum>i\<le>deg. x i * \<B>^i)"
      unfolding x_def
      by (metis (no_types, opaque_lifting) dual_order.strict_implies_order 
        e_b_bound(1) int_ops(7) nat_0_le nat_int)
    finally show ?thesis
      using Suc_eq_plus1 lessThan_Suc_atMost by presburger
  qed

  have y_sum: "(b-1) * \<B>^(n (\<nu>+1)) = (\<Sum>i<deg+1. y i * \<B>^i)"
  proof -
    have 0: "n (\<nu>+1) \<le> deg" unfolding deg_def n_def by auto

    have "(\<Sum>i\<in>{..deg}. y i * \<B>^i) = 
      (\<Sum>i\<in>{..deg} - {n (\<nu>+1)}. y i * \<B>^i) + (\<Sum>i\<in>{n (\<nu>+1)}. y i * \<B>^i)"
      by (meson "0" atMost_iff empty_subsetI finite_atMost insert_subset sum.subset_diff)
    also have "... = (\<Sum>i\<in>{n (\<nu>+1)}. y i * \<B>^i)"
      unfolding y_def by simp
    also have "... = y (n (\<nu>+1)) * \<B>^(n (\<nu>+1))"
      by simp
    also have "... = (b-1) * \<B>^(n (\<nu>+1))"
      unfolding y_def by simp
    finally show ?thesis
      using Suc_eq_plus1 lessThan_Suc_atMost by presburger
  qed

  have digit_cond: "x i + y i < \<B>" for i
  proof cases
    assume "i = n (\<nu>+1)" 
    hence "x i + y i \<le> b + (b - 1)"
      unfolding x_def y_def using assm by auto
    also have "... = \<B> - 1" 
      using b_def_reverse by auto
    also have "... < \<B>" 
      using \<B>_ge_1 by auto
    finally show ?thesis .
  next 
    assume "i \<noteq> n (\<nu>+1)"
    hence "x i + y i \<le> nat (e i + int b)"
      unfolding x_def y_def by auto
    also have "... < \<B>"
      using e_b_bound by (smt (verit) nat_less_iff)
    finally show ?thesis .
  qed
  
  have \<tau>_digits: "\<tau> (x i) (y i) = 0" for i
  proof cases 
    assume i_def: "i = n (\<nu>+1)" 
    obtain k where "b = 2^k" using b_power2 is_power2_def by auto
    thus ?thesis using assm unfolding x_def y_def i_def
      using nat_int plus_int_code(2) count_carries_pow2_block_ones count_carries_0n by presburger
  next 
    assume "i \<noteq> n (\<nu>+1)"
    thus ?thesis unfolding y_def by simp
  qed

  obtain k where k_def: "\<B> = 2^k"
    using \<B>_power2 is_power2_def by auto
  have k_ge_1: "1 \<le> k"
    using k_def \<B>_ge_2
    by (metis \<B>_gt_2 antisym linorder_linear one_le_numeral order_less_le 
        power_increasing power_one_right)

  have "\<tau> (nat K) ((b-1) * \<B>^(n (\<nu>+1))) = (\<Sum>i<deg+1. \<tau> (x i) (y i))"
    using count_carries_digitwise_no_overflow[OF k_ge_1] digit_cond k_def 
    unfolding x_sum y_sum by blast
  also have "... = 0" 
    using \<tau>_digits by simp
  finally show ?thesis .
qed

 
lemma reverse_implication:
  "\<tau> (nat K) ((b-1) * \<B>^(n (\<nu>+1))) = 0 \<Longrightarrow> insertion z_assign P = 0"
proof -
  assume assm: "\<tau> (nat K) ((b-1) * \<B>^(n (\<nu>+1))) = 0"
  
  define deg where "deg = (2*\<delta>+1) * n \<nu>"
  define x where "x = (\<lambda>i. nat (e i + int b))"
  define y where "y = (\<lambda>i. if i = n (\<nu>+1) then b-1 else 0)"
  
  have x_sum: "nat K = (\<Sum>i<deg+1. x i * \<B>^i)"
  proof -
    have 0: "(e i + int b) * \<B>^i \<ge> 0" for i
      using e_b_bound(1) by (simp add: dual_order.strict_implies_order)

    have "nat K = nat (\<Sum>i\<le>deg. (e i + int b) * \<B>^i)"
      unfolding K_expression deg_def by auto
    also have "... = (\<Sum>i\<le>deg. nat ((e i + int b) * \<B>^i))"
      using nat_sum_distrib 0 by auto
    also have "... = (\<Sum>i\<le>deg. x i * \<B>^i)"
      unfolding x_def
      by (metis (no_types, opaque_lifting) dual_order.strict_implies_order 
        e_b_bound(1) int_ops(7) nat_0_le nat_int)
    finally show ?thesis
      using Suc_eq_plus1 lessThan_Suc_atMost by presburger
  qed

  have y_sum: "(b-1) * \<B>^(n (\<nu>+1)) = (\<Sum>i<deg+1. y i * \<B>^i)"
  proof -
    have 0: "n (\<nu>+1) \<le> deg" unfolding deg_def n_def by auto

    have "(\<Sum>i\<in>{..deg}. y i * \<B>^i) = 
      (\<Sum>i\<in>{..deg} - {n (\<nu>+1)}. y i * \<B>^i) + (\<Sum>i\<in>{n (\<nu>+1)}. y i * \<B>^i)"
      by (meson "0" atMost_iff empty_subsetI finite_atMost insert_subset sum.subset_diff)
    also have "... = (\<Sum>i\<in>{n (\<nu>+1)}. y i * \<B>^i)"
      unfolding y_def by simp
    also have "... = y (n (\<nu>+1)) * \<B>^(n (\<nu>+1))"
      by simp
    also have "... = (b-1) * \<B>^(n (\<nu>+1))"
      unfolding y_def by simp
    finally show ?thesis
      using Suc_eq_plus1 lessThan_Suc_atMost by presburger
  qed

  have xy_bound: "x i < \<B> \<and> y i < \<B>" for i
    unfolding x_def y_def using e_b_bound b_def
    by (smt (verit, best) \<B>_ge_1 div_less_dividend less_imp_diff_less less_numeral_extra(1) 
        nat_less_iff one_less_numeral_iff order_less_le_trans semiring_norm(76))

  obtain k where k_def: "\<B> = 2^k"
    using \<B>_power2 is_power2_def by auto
  have k_ge_1: "1 \<le> k"
    using k_def \<B>_ge_2
    by (metis \<B>_gt_2 antisym linorder_linear one_le_numeral order_less_le 
        power_increasing power_one_right)

  have "n (\<nu>+1) < deg+1"
    unfolding deg_def n_def by auto
  hence "\<tau> (x (n (\<nu>+1))) (y (n (\<nu>+1))) \<le> \<tau> (\<Sum>i<deg+1. x i * \<B>^i) (\<Sum>i<deg+1. y i * \<B>^i)"
    using count_carries_digitwise_specific[OF k_ge_1] xy_bound 
    unfolding k_def by meson
  hence "\<tau> (x (n (\<nu>+1))) (y (n (\<nu>+1))) = 0"
    using x_sum y_sum assm by auto
  hence "\<tau> (b-1) (nat (e (n (\<nu>+1)) + int b)) = 0"
    using x_def y_def n_def deg_def count_carries_sym by simp
  hence "b dvd nat (e (n (\<nu>+1)) + int b)"
    using count_carries_divisibility_pow2 b_power2 unfolding is_power2_def by force
  hence "(int b) dvd (e (n (\<nu>+1)) + int b)"
    by (metis dual_order.strict_iff_not e_b_bound(1) nat_0_le of_nat_dvd_iff)
  hence b_dvd_e: "b dvd e (n (\<nu>+1))"
    by auto
  hence "e (n (\<nu>+1)) = 0"
  proof cases
    assume "e (n (\<nu>+1)) = 0" thus ?thesis .
  next 
    assume "e (n (\<nu>+1)) \<noteq> 0"
    hence "b \<le> abs (e (n (\<nu>+1)))"
      using b_dvd_e by (simp add: zdvd_imp_le) 
    hence "\<B> \<le> 2 * abs (e (n (\<nu>+1)))"
      using b_def_reverse by auto
    hence "fact \<delta> * (nat L) * (1 + sum_list z)^\<delta> < abs (e (n (\<nu>+1)))"
      using \<B>_lower_bound by linarith
    thus ?thesis
      using e_upper_bound L_pos dual_order.strict_iff_not
      by fastforce
  qed
  thus ?thesis using e_n_\<nu>1_expression by auto
qed

lemma tau_rewrite: 
  "\<tau> (2 * nat K) ((\<B>-2) * \<B>^(n (\<nu>+1))) = \<tau> (nat K) ((b-1) * \<B>^(n (\<nu>+1)))"
  using count_carries_even_even b_def_reverse
  by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) mult_numeral_1_right numerals(1) 
      right_diff_distrib')
 
lemma lemma_1_8: 
  shows "insertion z_assign P = 0 \<longleftrightarrow> \<tau> (2 * nat K) ((\<B>-2) * \<B>^(n (\<nu>+1))) = 0"
    and "K > int \<B>^((2*\<delta>+1) * n \<nu>)" 
    and "K < int \<B>^((2*\<delta>+1) * n \<nu> + 1)"
  using K_lower_bound K_upper_bound direct_implication reverse_implication n_def tau_rewrite
  by simp_all blast

end

end
