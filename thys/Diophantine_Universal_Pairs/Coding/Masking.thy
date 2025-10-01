theory Masking
  imports Complex_Main Bit_Counting Utils
begin

subsection \<open>Masking\<close>

abbreviation \<sigma> where "\<sigma> \<equiv> count_bits"
abbreviation \<tau> where "\<tau> \<equiv> count_carries"

locale masking_lemma =
  fixes \<delta> \<nu> \<B> b C :: nat 
  assumes \<delta>_pos: "\<delta> > 0"
      and \<B>_power2: "is_power2 (int \<B>)" 
      and b_power2: "is_power2 (int b)"
      and \<B>_ge_2: "2 \<le> \<B>" 
      and b_le_\<B>: "b \<le> \<B>"
      and C_lower_bound: "C \<ge> b * \<B>^(\<delta>+1)^\<nu>"
      and C_upper_bound: "C \<le> \<B> * \<B>^(\<delta>+1)^\<nu>"
begin

definition n :: "nat \<Rightarrow> nat" where "n j = (\<delta>+1)^j"

definition m::"nat \<Rightarrow> nat" where
"m j = (if j \<in> n ` {1..\<nu>} then \<B> - b else \<B> - 1)"

text \<open>\<open>mask(b, \<B>, \<delta>, \<nu>)\<close>\<close>
definition M::nat where "M = (\<Sum>j=0..n \<nu>. m j * \<B>^j)" 

lemma b_ge_1: "1 \<le> b"
  using b_power2 is_power2_ge1 by force
    
lemma b_dvd_\<B>: "b dvd \<B>" 
  using b_le_\<B> b_power2 \<B>_power2 is_power2_def le_imp_power_dvd by fastforce   

lemma n_inj_on: "inj_on n A"
  unfolding n_def inj_on_def by (simp add: \<delta>_pos)

lemma direct_g_bound:
  assumes z_bound: "\<forall>i. z i < b"
      and g_code: "g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))"
  shows "g < C" 
proof (cases "b > 1")
  case False 
  hence "b = 1" using b_ge_1 by simp
  hence "g = 0" using z_bound g_code by simp
  thus ?thesis using C_lower_bound b_ge_1 \<B>_ge_2 using zero_less_iff_neq_zero by fastforce
next
  case True

  define z' where "z' = (\<lambda>j. if j \<in> range n then z (inv n j) else 0)"

  have z'_bound: "z' j \<le> b - 1" for j
    unfolding z'_def using z_bound b_ge_1 less_Suc_eq_le by fastforce

  have "g = (\<Sum>i\<in>{1..\<nu>}. z' (n i) * \<B>^(n i))"
    using sum.cong z'_def n_inj_on by (simp add: g_code)
  also have "... = (\<Sum>j\<in>n`{1..\<nu>}. z' j * \<B>^j)"
    using n_inj_on[of "{1..\<nu>}"] by (simp add: sum.reindex_cong)
  also have "... \<le> (\<Sum>j\<in>{0..n \<nu>}. z' j * \<B>^j)"
  proof -
    have "n ` {1..\<nu>} \<subseteq> {0..n \<nu>}" 
      unfolding n_def
      by (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 Suc_le_mono atLeast0AtMost 
          atLeastAtMost_iff image_subset_iff power_increasing zero_le)
    thus ?thesis using sum_mono2 by blast
  qed
  also have "... \<le> (\<Sum>j=0..n \<nu>. (b - 1) * \<B>^j)"
    using z'_bound sum_mono by (metis (no_types, lifting) mult_le_cancel2)
  finally have "g \<le> (b-1) * (\<Sum>j<(n \<nu>)+1. \<B>^j)"
    using sum_distrib_left by (metis Suc_eq_plus1 atMost_atLeast0 lessThan_Suc_atMost)
  
  hence "(\<B>-1) * g \<le> (\<B>-1) * (\<Sum>j<(n \<nu>)+1. \<B>^j) * (b-1)"
    by (simp add: mult.commute)
  also have "... = (\<B>^(n \<nu> + 1) - 1) * (b-1)"
    using aux_geometric_sum \<B>_ge_2
    by (metis le_imp_less_Suc nat_add_left_cancel_less one_add_one plus_1_eq_Suc)
  also have "... < (b-1) * \<B> * \<B>^(n \<nu>)"
    using True \<B>_ge_2 by auto
  also have "... \<le> (\<B>-1) * b * \<B>^(n \<nu>)"
    using b_le_\<B> \<B>_ge_2
    by (smt (verit) diff_le_mono2 diff_mult_distrib mult.commute mult_le_mono1)
  finally have "g < b * \<B>^(n \<nu>)" 
    by auto
  thus ?thesis
    using C_lower_bound n_def by simp
qed

lemma direct_tau_zero:
  assumes z_bound: "\<forall>i. z i < b"
      and g_code: "g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))"
  shows "\<tau> g M = 0"
proof -
  define z' where "z' = (\<lambda>j. if j \<in> n ` {1..\<nu>} then z (inv n j) else 0)"

  have "g = (\<Sum>i\<in>{1..\<nu>}. z' (n i) * \<B>^(n i))"
    using sum.cong z'_def n_inj_on by (simp add: g_code)
  also have "... = (\<Sum>j\<in>n`{1..\<nu>}. z' j * \<B>^j)"
    using n_inj_on[of "{1..\<nu>}"] by (simp add: sum.reindex_cong)
  also have "... = (\<Sum>j\<in>{0..n \<nu>}. z' j * \<B>^j)"
  proof -
    have "n ` {1..\<nu>} \<subseteq> {0..n \<nu>}"
      unfolding n_def
      by (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 Suc_le_mono atLeast0AtMost 
          atLeastAtMost_iff image_subset_iff power_increasing zero_le)
    moreover have "j \<in> {0..n \<nu>} - n ` {1..\<nu>} \<Longrightarrow> z' j * \<B>^j = 0" for j
      unfolding z'_def by auto
    ultimately show ?thesis
      using sum.mono_neutral_left by (simp add: sum.subset_diff)
  qed
  finally have g_sum: "g = (\<Sum>j<n \<nu> + 1. z' j * \<B>^j)"
    using Suc_eq_plus1 atLeast0AtMost lessThan_Suc_atMost by presburger
  
  have zm_bound: "z' j + m j < \<B>" for j
    unfolding z'_def m_def using b_le_\<B> z_bound \<B>_ge_2
    by (smt (verit, best) add_diff_inverse_nat add_le_cancel_right b_ge_1 dual_order.strict_trans2 
        linorder_not_less zero_less_one)
 
  have tau_digits: "\<tau> (z' j) (m j) = 0" for j
  proof (cases "j \<in> n ` {1.. \<nu>}")
    case False thus ?thesis unfolding z'_def by simp
  next
    obtain k where k_def: "b = 2^k" using b_power2 is_power2_def by auto

    case True
    hence "\<tau> (z' j) (m j) = \<tau> (z (inv n j)) (\<B> - b)"
      using z'_def m_def by simp
    also have "... = \<tau> (z (inv n j) + 0 * b) (0 + (\<B> div b - 1) * b)"
      using b_dvd_\<B> by (simp add: mult.commute right_diff_distrib')
    also have "... = \<tau> (z (inv n j)) 0 + \<tau> 0 (\<B> div b - 1)"
      using count_carries_add_shift_no_overflow k_def z_bound
      by (metis (no_types, lifting) add.right_neutral)
    also have "... = 0" 
      by simp
    finally show ?thesis .
  qed

  obtain k where k_def: "\<B> = 2^k"
    using \<B>_power2 is_power2_def by auto
  have k_ge_1: "1 \<le> k"
    using k_def \<B>_ge_2
    by (metis Suc_eq_plus1 Suc_leD antisym div_le_dividend div_self nat_1_add_1 numeral_eq_one_iff 
        order_refl power_0 semiring_norm(85))

  have "\<tau> g M = \<tau> (\<Sum>j<n \<nu> + 1. z' j * \<B>^j) (\<Sum>j<n \<nu> + 1. m j * \<B>^j)"
    using g_sum M_def Suc_eq_plus1 atLeast0AtMost lessThan_Suc_atMost by presburger
  also have "... = (\<Sum>j<n \<nu> + 1. \<tau> (z' j) (m j))"
    using count_carries_digitwise_no_overflow[OF k_ge_1] k_def zm_bound by blast
  also have "... = 0"
    using tau_digits by simp
  finally show ?thesis .
qed

lemma reverse_impl:
  assumes tau_zero: "\<tau> g M = 0"
      and g_bound_C: "g < C"
  shows "\<exists>z. (\<forall>i. z i < b) \<and> g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))"
proof -
  have g_bound_\<B>: "g < \<B>^(n \<nu> + 1)"
    using C_upper_bound g_bound_C n_def by simp
 
  have g_digit: "j > n \<nu> \<Longrightarrow> nth_digit g j \<B> = 0" for j
    using nth_digit_def \<B>_ge_2 g_bound_\<B>
    by (metis Suc_eq_plus1 div_less linorder_not_less mod_less nat_1_add_1 not_less_eq_eq 
        order_less_le_trans power_increasing_iff zero_less_two)
  have g_sum: "g = (\<Sum>j<n \<nu> + 1. nth_digit g j \<B> * \<B>^j)"
    using digit_gen_sum_repr[OF g_bound_\<B>] \<B>_ge_2 by auto

  have digit_bound: "j \<in> {0..n \<nu>} \<Longrightarrow> nth_digit g j \<B> + m j < \<B>" for j
  proof -
    obtain k where k_def: "\<B> = 2^k"
      using \<B>_power2 is_power2_def by auto
    have k_ge_1: "1 \<le> k"
      using k_def \<B>_ge_2
      by (metis Suc_eq_plus1 Suc_leD antisym div_le_dividend div_self nat_1_add_1 numeral_eq_one_iff 
          order_refl power_0 semiring_norm(85))
    assume "j \<in> {0..n \<nu>}"
    hence "j < n \<nu> + 1" 
      by auto
    moreover have 0: "m j < \<B> \<and> nth_digit g j \<B> < \<B>" for j
      unfolding m_def nth_digit_def using \<B>_ge_2 b_ge_1 by fastforce
    ultimately have "\<tau> (\<Sum>j<n \<nu> + 1. nth_digit g j \<B> * \<B>^j) (\<Sum>j<n \<nu> + 1. m j * \<B>^j) \<ge> 
      \<tau> (nth_digit g j \<B>) (m j)"
      using count_carries_digitwise_specific[OF k_ge_1 _ `j < n \<nu> + 1`] k_def by force
    hence "\<tau> (nth_digit g j \<B>) (m j) = 0"
      using tau_zero g_sum M_def
      by (metis Suc_eq_plus1 atLeast0AtMost le_zero_eq lessThan_Suc_atMost)
    thus ?thesis
      using no_carry_no_overflow k_def 0 by auto
  qed
 
  define z where "z = (\<lambda>j. nth_digit g (n j) \<B>)"
 
  have digit_zero: "j \<notin> n ` {1..\<nu>} \<Longrightarrow> nth_digit g j \<B> = 0" for j
  proof (cases "j \<in> {0..n \<nu>}")
    case False thus ?thesis using g_digit by auto
  next
    case True
    assume assm: "j \<notin> n ` {1..\<nu>}"
    have "nth_digit g j \<B> + m j < \<B>"
      using True digit_bound by simp
    hence "nth_digit g j \<B> + (\<B> - 1) < \<B>"
      using m_def assm by auto
    thus ?thesis
      using nth_digit_def by simp
  qed

  have z_bound: "z i < b" for i
  proof (cases "i \<in> {1..\<nu>}")
    case False
    hence "(n i) \<notin> n ` {1..\<nu>}"
      using n_inj_on by blast
    hence "nth_digit g (n i) \<B> = 0"
      unfolding z_def using digit_zero by auto
    thus ?thesis 
      using b_ge_1 z_def by auto
  next
    case True
    hence "n i \<in> {0..n \<nu>}"
      unfolding n_def by (simp add: power_increasing)
    hence "z i + m (n i) < \<B>"
      using digit_bound z_def by auto
    hence "z i + (\<B> - b) < \<B>"
      using m_def by (metis True imageI)
    thus "z i < b" 
      using b_le_\<B> by auto
  qed

  have g_sum_z: "g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))" 
  proof -
    have "g = (\<Sum>j\<in>{0..n \<nu>}. nth_digit g j \<B> * \<B>^j)"
      using g_sum by (metis Suc_eq_plus1 atLeast0AtMost lessThan_Suc_atMost)
    also have "... = (\<Sum>j\<in>n`{1..\<nu>}. nth_digit g j \<B> * \<B>^j)"
    proof -
      have "n ` {1..\<nu>} \<subseteq> {0..n \<nu>}"
        unfolding n_def
        by (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 Suc_le_mono atLeast0AtMost 
            atLeastAtMost_iff image_subset_iff power_increasing zero_le)
      moreover have "j \<in> {0..n \<nu>} - n ` {1..\<nu>} \<Longrightarrow> nth_digit g j \<B>  * \<B>^j = 0" for j
        using digit_zero by auto
      ultimately show ?thesis 
        using sum.mono_neutral_right by (metis (no_types, lifting) finite_atLeastAtMost)
    qed
    also have "... = (\<Sum>i\<in>{1..\<nu>}. nth_digit g (n i) \<B> * \<B>^(n i))"
      using n_inj_on sum.reindex by auto
    finally show ?thesis 
      using z_def by simp
  qed

  show ?thesis
    using z_bound g_sum_z by auto 
qed

lemma masking_lemma:
  "(\<exists>z. (\<forall>i. z i < b) \<and> g = (\<Sum>i=1..\<nu>. z i * \<B>^(n i))) \<longleftrightarrow> (g < C \<and> \<tau> g M = 0)"
  using reverse_impl direct_tau_zero direct_g_bound by auto

end

end