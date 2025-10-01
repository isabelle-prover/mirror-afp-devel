theory Bit_Counting
  imports Digit_Expansions.Binary_Operations "HOL-Computational_Algebra.Primes"
begin

section \<open>The Coding Technique\<close>

subsection \<open>Counting bits and number of carries\<close>

text \<open>Count the number of bits in the binary expansion of n\<close>

definition bit_set :: "nat \<Rightarrow> nat set" where 
  "bit_set n = {i. n \<exclamdown> i = 1}"

definition count_bits :: "nat \<Rightarrow> nat" where 
  "count_bits n = card (bit_set n)"

text \<open>Count the number of carries in the binary addition of a and b\<close>

definition carry_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where 
  "carry_set a b = {i. bin_carry a b i = 1}"

definition count_carries :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "count_carries a b = card (carry_set a b)"

text \<open>This shows that \<open>{@const count_bits}\<close> is well defined\<close>

lemma bit_set_subset: "bit_set n \<subseteq> {..<n}"
proof -
  { fix i assume "i \<ge> n" 
    hence "n \<exclamdown> i = 0" unfolding nth_bit_def by (simp add: order_le_less_trans) }
  thus ?thesis
    unfolding bit_set_def
    by (metis (mono_tags, lifting) lessThan_iff dual_order.strict_iff_not mem_Collect_eq 
        nle_le subsetI zero_neq_one)
qed

corollary bit_set_finite: "finite (bit_set n)"
  using bit_set_subset finite_subset by fastforce

text \<open>We can be more precise when we know how many bits n requires\<close>

lemma bit_set_subset_variant:  "n < 2^k \<Longrightarrow> bit_set n \<subseteq> {..<k}"
proof -
  assume "n < 2^k"
  hence "i \<ge> k \<Longrightarrow> n \<exclamdown> i = 0" for i
    by (metis add.commute add_cancel_left_right aux1_digit_lt_linear aux1_digit_wise_equiv mult_0)
  thus ?thesis
    unfolding bit_set_def
    by (metis (mono_tags, lifting) One_nat_def lessThan_iff less_le_not_le 
        linorder_neqE_nat mem_Collect_eq nat.simps(3) order_refl subsetI)
qed

corollary count_bits_def_sum: "n < 2^k \<Longrightarrow> count_bits n = (\<Sum>i<k. n \<exclamdown> i)"
proof -
  assume assm: "n < 2^k"
 
  have "(\<Sum>i<k. n \<exclamdown> i) = (\<Sum>i\<in>{..<k}. of_bool (n \<exclamdown> i = 1))"
    by (smt (verit, del_insts) sum.cong not_mod_2_eq_1_eq_0 nth_bit_def of_bool_eq(1) of_bool_eq(2))
  also have "... = card ({..<k} \<inter> bit_set n)"
    unfolding bit_set_def using Groups_Big.sum_of_bool_eq finite_lessThan by simp
  also have "... = count_bits n"
    unfolding count_bits_def using bit_set_subset_variant[OF assm] by (simp add: inf.absorb2)
  finally show ?thesis by simp
qed

corollary count_bits_bounded: "n < 2^k \<Longrightarrow> count_bits n \<le> k"
  unfolding count_bits_def using bit_set_subset_variant
  by (metis card_lessThan card_mono finite_lessThan)

text \<open>The following lemma shows that \<open>{@const count_carries}\<close> is well defined\<close>

lemma carry_set_subset: "carry_set a b \<subseteq> {..max a b}"
proof -
  { fix i assume "i > max a b"
    hence "i > a" and "i > b" 
      by simp_all
    have "a < 2^(i-1)" using `i > a`
      by (metis Suc_diff_1 Suc_leI gr_implies_not0 less_exp not_le_imp_less order_less_le_trans)
    moreover have "b < 2^(i-1)" using `i > b`
      by (metis Suc_diff_1 Suc_leI gr_implies_not0 less_exp not_le_imp_less order_less_le_trans)
    ultimately have "a + b < 2^(Suc (i-1))"
      by simp
    hence ab_bound: "a + b < 2^i"
      using `i > a` by simp
     
    have "(a mod 2^i) + (b mod 2^i) = a + b"
      using `i > a` `i > b` by (metis less_exp less_imp_add_positive mod_less trans_less_add1)
    hence "bin_carry a b i = 0"
      unfolding bin_carry_def using ab_bound by simp }
  thus ?thesis
    unfolding carry_set_def
    by (metis (mono_tags, lifting) atMost_iff mem_Collect_eq subsetI 
        verit_comp_simplify1(3) zero_neq_one)  
qed

corollary carry_set_finite: "finite (carry_set a b)"
  using carry_set_subset finite_subset by blast

text \<open>We can be more precise when we know how many bits $a+b$ requires\<close>

lemma carry_set_subset_variant: "a + b < 2^k \<Longrightarrow> carry_set a b \<subseteq> {..<k}"
proof -
  assume assm: "a + b < 2^k"
  hence "i \<ge> k \<Longrightarrow> bin_carry a b i = 0" for i
    unfolding bin_carry_def
    using Euclidean_Rings.div_eq_0_iff add_increasing add_increasing2 div_exp_eq 
        le_antisym le_eq_less_or_eq le_iff_add mod_eq_self_iff_div_eq_0 zero_le
    by (smt (verit, ccfv_threshold) div_greater_zero_iff)
  thus ?thesis
    unfolding carry_set_def
    by (metis (full_types, lifting) lessThan_iff linorder_not_less mem_Collect_eq 
        subsetI zero_neq_one)
qed

corollary count_carries_def_sum: "a + b < 2^k \<Longrightarrow> count_carries a b = (\<Sum>i<k. bin_carry a b i)"
proof -
  assume assm: "a + b < 2^k"
 
  have "(\<Sum>i<k. bin_carry a b i) = (\<Sum>i\<in>{..<k}. of_bool (bin_carry a b i = 1))"
    using sum.cong bin_carry_def
    by (smt (verit, best) bin_carry_bounded not_mod_2_eq_0_eq_1 of_bool_eq(1) of_bool_eq(2))   
 also have "... = card ({..<k} \<inter> carry_set a b)"
    unfolding carry_set_def using Groups_Big.sum_of_bool_eq finite_lessThan by simp
  also have "... = count_carries a b"
    unfolding count_carries_def using carry_set_subset_variant[OF assm] by (simp add: inf.absorb2)
  finally show ?thesis by auto
qed

text \<open>Some elementary properties of \<open>{@const count_bits}\<close> and \<open>{@const count_carries}\<close>\<close>

lemma bit_set_0[simp]: "bit_set 0 = {}"
  unfolding bit_set_def nth_bit_def by simp

corollary count_bits_0[simp]: "count_bits 0 = 0"
  unfolding count_bits_def by simp

lemma bit_set_1[simp]: "bit_set 1 = {0}"
proof -  
  have bit_one: "1 \<exclamdown> i = (if i = 0 then 1 else 0)" for i
    unfolding nth_bit_def
    using div_eq_0_iff bits_one_mod_two_eq_one gr_zeroI mod_0 
        one_div_two_eq_zero one_less_power power_0 zero_neq_numeral 
    by (metis div_by_1)
  thus ?thesis unfolding bit_set_def bit_one by simp
qed

corollary count_bits_1[simp]: "count_bits 1 = 1"
  unfolding count_bits_def bit_set_1 by simp

lemma carry_set_n0[simp]: "carry_set n 0 = {}" 
  unfolding carry_set_def bin_carry_def by simp
lemma carry_set_0n[simp]: "carry_set 0 n = {}" 
  unfolding carry_set_def bin_carry_def by simp

corollary count_carries_n0[simp]: "count_carries n 0 = 0"
  unfolding count_carries_def by simp
corollary count_carries_0n[simp]: "count_carries 0 n = 0"
  unfolding count_carries_def by simp

lemma carry_set_sym: "carry_set a b = carry_set b a"
  unfolding carry_set_def bin_carry_def by (simp add: add.commute)

corollary count_carries_sym: "count_carries a b = count_carries b a"
  unfolding count_carries_def by (simp add: carry_set_sym)

lemma aux_geometric_sum: 
  "(x::nat) > 1 \<Longrightarrow> (x-1) * (\<Sum>i<n. x^i) = x^n - 1"
proof (induct n)
  case 0 show ?case using lessThan_0 by (simp add: algebra_simps)
next
  case (Suc n)
  have "(x-1) * (\<Sum>i<Suc n. x^i) = (x-1) * (\<Sum>i<n. x^i) + (x-1) * x^n"
    using add_mult_distrib2 by auto
  also have "... = x^n - 1 + x^(Suc n) - x^n"
    using Suc less_imp_Suc_add by fastforce
  also have "... = x^(Suc n) - 1"
    using Suc.prems by auto
  finally show ?case .
qed

lemma aux_digit_sum_bound: 
  assumes "1 < (b::nat)" and "\<forall>i<q. f i < b"
  shows "(\<Sum>i<q. f i * b^i) < b^q"
proof -
  have "i < q \<Longrightarrow> f i * b^i \<le> (b-1) * b^i" for i
    by (metis assms le_add_diff_inverse less_Suc_eq_le less_imp_le_nat mult_le_mono1 plus_1_eq_Suc)
  hence "(\<Sum>i<q. f i * b^i) \<le> (\<Sum>i<q. (b-1) * b^i)"
    by (meson lessThan_iff sum_mono)
  also have "... = b^q - 1"
    using sum_distrib_left aux_geometric_sum assms(1) by metis  
  finally show ?thesis
    by (metis assms(1) le_add_diff_inverse le_imp_less_Suc less_imp_le_nat one_le_power 
        plus_1_eq_Suc)
qed

lemma carry_set_same[simp]: "carry_set a a = Suc ` bit_set a"
  (is "?A = ?B")
proof -
  have 0: "bin_carry a a (Suc i) = a \<exclamdown> i" for i
    unfolding bin_carry_def nth_bit_def
    by (metis One_nat_def add.commute add_self_div_2 div_exp_eq div_exp_mod_exp_eq plus_1_eq_Suc 
        power_Suc0_right)

  have 1: "?A \<subseteq> ?B"
  proof 
    fix i assume i_def: "i \<in> carry_set a a"
    hence "i > 0"
      unfolding carry_set_def bin_carry_def using gr0I by force
    hence "a \<exclamdown> (i-1) = 1"
      using i_def 0 unfolding carry_set_def
      by (metis (mono_tags, lifting) One_nat_def Suc_pred mem_Collect_eq)
    thus "i \<in> ?B" 
      using bit_set_def Suc_pred' \<open>0 < i\<close> by blast
  qed

  have 2: "?B \<subseteq> ?A"
  proof 
    fix i assume i_def: "i \<in> ?B"
    hence "a \<exclamdown> (i-1) = 1"
      using bit_set_def by auto
    hence "bin_carry a a i = 1"
      using 0 i_def by fastforce
    thus "i \<in> ?A" 
      using carry_set_def by simp
  qed

  from 1 2 show ?thesis by simp
qed
  
corollary count_carries_same[simp]: "count_carries a a = count_bits a"
  using count_carries_def count_bits_def carry_set_same by (simp add: card_image)

lemma bit_set_pow2[simp]: "bit_set (2^k) = {k}"
proof -
  have "(2^k) \<exclamdown> i = (if i = k then 1 else 0)" for i
    unfolding nth_bit_def
    by (metis Suc_mask_eq_exp bit_exp_iff bit_iff_odd nat.simps(3) not_mod_2_eq_1_eq_0 
        odd_iff_mod_2_eq_one possible_bit_def)
  thus ?thesis unfolding bit_set_def by simp
qed

corollary count_bits_pow2[simp]: "count_bits (2^k) = 1"
  unfolding count_bits_def by simp

lemma bit_set_block_ones[simp]: "bit_set (2^k - 1) = {..<k}"
proof -
  have bit: "(2^k - 1) \<exclamdown> i = (if i < k then 1 else 0)" for i
    unfolding nth_bit_def
    by (meson even_decr_exp_div_exp_iff' mod2_eq_if not_less) 
  
  hence "bit_set (2^k - 1) = bit_set (2^k-1) \<inter> {..<k}"
    unfolding count_bits_def using bit_set_subset_variant by (simp add: inf_absorb1)
  also have "... = {i. (2^k-1) \<exclamdown> i = 1 \<and> i < k}"
    unfolding bit_set_def by (simp add: Collect_conj_eq lessThan_def)
  also have "... = {i. i < k}"
    unfolding bit by simp
  finally show ?thesis
    by auto
qed

corollary count_bits_block_ones[simp]: "count_bits (2^k-1) = k"
  unfolding count_bits_def bit_set_block_ones by simp

text \<open>The binary complement of a number with k bits\<close>
lemma nth_bit_complement:
  "a < 2^k \<Longrightarrow> (2^k-1-a) \<exclamdown> i = (if i < k then 1 - (a \<exclamdown> i) else 0)"
proof (cases "k = 0")
  case True assume "a < 2^k" 
  hence "a = 0" using True by simp
  thus ?thesis using True nth_bit_def by simp
next
  case False assume assm: "a < 2^k"
  have 0: "\<forall>i. (a \<exclamdown> i) * 2^i \<le> 2^i" using nth_bit_bounded by simp
  have 1: "\<forall>i. 1 - (a \<exclamdown> i) < 2^(Suc 0)" by auto
  have 2: "k = Suc (k-1)" using False by simp

  have "2^k-1-a = (2^k - 1) - (\<Sum>i<k. (a \<exclamdown> i) * 2^i)"
    using digit_sum_repr[OF assm] by simp
  also have "... = (\<Sum>i<k. 2^i) - (\<Sum>i<k. (a \<exclamdown> i) * 2^i)"
    using aux_geometric_sum[of "2::nat"] by simp
  also have "... = (\<Sum>i<k. 2^i - (a \<exclamdown> i) * 2^i)"
    using sum_diff_distrib[OF 0] .
  also have "... = (\<Sum>i<k. (1 - a \<exclamdown> i) * 2^i)"
    using nth_bit_bounded
    by (metis (no_types, opaque_lifting) cancel_comm_monoid_add_class.diff_cancel diff_zero 
        mult.commute mult.right_neutral mult_zero_right not_mod_2_eq_1_eq_0 nth_bit_def)
  finally have complement: "2^k-1-a = (\<Sum>i=0..k-1. (1 - a \<exclamdown> i) * 2^i)"
    using 2 by (metis atLeast0LessThan atLeastLessThanSuc_atLeastAtMost)

  have "(2^k-1-a) \<exclamdown> i = (if i \<le> k-1 then 1 - a \<exclamdown> i else 0)"
    using nth_digit_gen_power_series[OF 1] 
    unfolding complement nth_digit_base2_equiv by simp
  thus ?thesis using False by simp
qed

lemma bit_set_complement:
  "a < 2^k \<Longrightarrow> bit_set (2^k-1-a) = {..<k} - bit_set a"
proof 
  assume assm: "a < 2^k"
  show "bit_set (2^k-1-a) \<subseteq> {..<k} - bit_set a"
  proof
    fix i assume i_def: "i \<in> bit_set (2^k-1-a)"
    hence "i < k" 
      by (metis (mono_tags, lifting) One_nat_def assm bit_set_def mem_Collect_eq 
         nat.simps(3) nth_bit_complement)
    thus "i \<in> {..<k} - bit_set a"
      using nth_bit_complement i_def unfolding bit_set_def by (simp add: assm)
  qed
next
  assume assm: "a < 2^k"
  show "{..<k} - bit_set a \<subseteq> bit_set (2^k-1-a)" 
  proof 
    fix i assume "i \<in> {..<k} - bit_set a"
    thus "i \<in> bit_set (2^k-1-a)"
      using bit_set_def nth_bit_complement[OF assm] by (simp add: nth_bit_def)
  qed
qed

corollary count_bits_complement: 
  "a < 2^k \<Longrightarrow> count_bits (2^k-1-a) = k - count_bits a"
  unfolding count_bits_def using bit_set_complement bit_set_subset_variant
  by (simp add: bit_set_finite card_Diff_subset)

lemma carry_set_pow2_block_ones[simp]: "carry_set (2^k) (2^k-1) = {}"
proof -
  have "bin_carry (2^k) (2^k-1) i = 0" for i
  proof (induct i)
    case 0 show ?case unfolding bin_carry_def by simp
  next 
    case (Suc i) 
    have "i < k \<Longrightarrow> (2^k) \<exclamdown> i + (2^k-1) \<exclamdown> i = 1"
      using bit_set_pow2 bit_set_block_ones nth_bit_bounded unfolding bit_set_def
      by (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 lessThan_iff mem_Collect_eq 
          nat_less_le not_mod_2_eq_1_eq_0 nth_bit_def singletonD)
    moreover have "i = k \<Longrightarrow> (2^k) \<exclamdown> i + (2^k-1) \<exclamdown> i = 1"
      using bit_set_pow2 bit_set_block_ones nth_bit_bounded unfolding bit_set_def
      by (simp add: nth_bit_def)
    moreover have "i > k \<Longrightarrow> (2^k) \<exclamdown> i + (2^k-1) \<exclamdown> i = 0"
      using nth_bit_bounded unfolding bit_set_def
      using add.right_neutral diff_less div_less less_exp linorder_not_less 
          nat_less_le not_mod_2_eq_1_eq_0 nth_bit_def odd_iff_mod_2_eq_one power_one_right 
          power_strict_increasing_iff
      by (metis even_decr_exp_div_exp_iff')
    ultimately show ?case
      using sum_carry_formula Suc by force
  qed
  thus ?thesis unfolding carry_set_def by simp
qed

corollary count_carries_pow2_block_ones[simp]:  "count_carries (2^k) (2^k-1) = 0"
  unfolding count_carries_def carry_set_pow2_block_ones by simp

lemma bit_set_add_shift:
  "a < 2^k \<Longrightarrow> bit_set (a + b * 2^k) = bit_set a \<union> ((+) k) ` bit_set b"
  (is "_ \<Longrightarrow> ?A = ?B")
proof
  assume assm: "a < 2^k" show "?A \<subseteq> ?B"
  proof 
    fix i assume "i \<in> ?A"
    hence i_def: "(a + b * 2^k) \<exclamdown> i = 1"
      using bit_set_def by simp
    { assume "i < k" 
      hence "a \<exclamdown> i = 1"
        using aux2_digit_sum_repr[OF assm] i_def by (simp add: add.commute)
      hence "i \<in> bit_set a" 
        using bit_set_def by simp }
    note 0 = this
    { assume "i \<ge> k" 
      hence "(b * 2^k) \<exclamdown> i = 1"
        using aux1_digit_lt_linear[OF assm] i_def by (simp add: add.commute) 
      hence "b \<exclamdown> (i-k) = 1"
        using aux_digit_shift by (metis \<open>k \<le> i\<close> le_add_diff_inverse2)
      hence "i \<in> ((+) k) ` bit_set b"
        using \<open>k \<le> i\<close> bit_set_def image_iff by fastforce }
    note 1 = this
    from 0 1 show "i \<in> ?B" by force
  qed
next
  assume assm: "a < 2^k" show "?B \<subseteq> ?A"
  proof 
    fix i assume "i \<in> ?B"
    hence i_def: "(a \<exclamdown> i = 1 \<and> i < k) \<or> (b \<exclamdown> (i-k) = 1 \<and> i \<ge> k)"
      using bit_set_subset_variant[OF assm] unfolding bit_set_def by auto
    thus "i \<in> ?A"
    proof
      assume "a \<exclamdown> i = 1 \<and> i < k"
      hence "(a + b * 2^k) \<exclamdown> i = 1"
        using aux2_digit_sum_repr[OF assm] by (simp add: add.commute)
      thus ?thesis 
        using bit_set_def by simp
    next
      assume "b \<exclamdown> (i-k) = 1 \<and> i \<ge> k"
      hence "(a + b * 2^k) \<exclamdown> i = 1"
        using aux1_digit_lt_linear[OF assm] aux_digit_shift 
        by (metis add.commute le_add_diff_inverse2) 
      thus ?thesis
        using bit_set_def by simp
    qed
  qed
qed
    
corollary count_bits_add_shift: 
  "a < 2^k \<Longrightarrow> count_bits (a + b * 2^k) = count_bits a + count_bits b"
proof -
  assume assm: "a < 2^k"
  
  have disjoint: "bit_set a \<inter> ((+) k) ` bit_set b = {}"
  proof -
    { fix i assume "i \<in> bit_set a \<inter> ((+) k) ` bit_set b"
      hence "i < k \<and> i \<ge> k"
        using bit_set_subset_variant[OF assm] by blast
      hence "False" by auto }
    thus ?thesis by blast
  qed

  have "count_bits (a + b * 2^k) = count_bits a + card (((+) k) ` bit_set b)"
    unfolding count_bits_def using bit_set_add_shift[OF assm] disjoint
    by (simp add: bit_set_finite card_Un_Int)
  also have "... = count_bits a + count_bits b"
    unfolding count_bits_def by (metis card_image inj_on_add)
  finally show ?thesis .
qed

corollary count_bits_even[simp]: "count_bits (2*n) = count_bits n"
  using count_bits_add_shift count_bits_0
  by (metis add_lessD1 comm_monoid_add_class.add_0 less_exp mult.commute power_one_right)

corollary count_bits_odd[simp]: "count_bits (2*n+1) = 1 + count_bits n"
  using count_bits_add_shift count_bits_1
  by (metis add.commute less_exp mult.commute power_one_right)

lemma count_bits_digitwise: 
  assumes "1 \<le> k" and "\<forall>i<q. f i < 2^k"
  shows "count_bits (\<Sum>i<q. f i * (2^k)^i) = (\<Sum>i<q. count_bits (f i))"
using assms
proof (induct q)
  case 0 show ?case by simp
next
  case (Suc q)
  have 0: "1 < (2::nat)^k" 
    using assms(1) by (meson dual_order.strict_trans2 less_exp)
  hence bound: "(\<Sum>i<q. f i * (2^k)^i) < 2^(k*q)"
    using aux_digit_sum_bound[OF 0] Suc.prems(2) power_mult
    by (metis (full_types) less_Suc_eq_le less_imp_le_nat)

  have "count_bits (\<Sum>i<Suc q. f i * (2^k)^i) = 
    count_bits ((\<Sum>i<q. f i * (2^k)^i) + f q * 2^(k*q))"
    by (simp add: power_mult)
  also have "... = count_bits (\<Sum>i<q. f i * (2^k)^i) + count_bits (f q)"
    using count_bits_add_shift[OF bound] by simp
  also have "... = (\<Sum>i<Suc q. count_bits (f i ))"
    using Suc by simp
  finally show ?case .
qed

lemma count_carries_count_bits:
  "count_bits (a+b) + count_carries a b = count_bits a + count_bits b"
proof -
  obtain k where k_def: "a + b < 2^k" using less_exp by blast
  
  have 0: "(\<Sum>i<k. bin_carry a b (i+1)) = (\<Sum>i<k. bin_carry a b i)"
  proof -
    have carry_0: "bin_carry a b 0 = 0"
      using bin_carry_def by auto
    
    have carry_k: "bin_carry a b k = 0"
      by (metis (no_types, lifting) div_eq_0_iff add.commute add_lessD1 
          bin_carry_def k_def mod_less)
    
    have "(\<Sum>i<k. bin_carry a b (i+1)) = (\<Sum>i=1..<k+1. bin_carry a b i)"
      by (metis add_0 atLeast0LessThan sum.shift_bounds_nat_ivl)
    also have "... = bin_carry a b 0 + (\<Sum>i=1..<k. bin_carry a b i)+ bin_carry a b k"
      using carry_0 by auto
    also have "... = (\<Sum>i<k. bin_carry a b i)"
      using carry_k by (simp add: atLeast0LessThan carry_0 sum_shift_lb_Suc0_0_upt)
    finally show ?thesis .
  qed

  have "(a + b) \<exclamdown> i + 2 * bin_carry a b (i+1) = a \<exclamdown> i + b \<exclamdown> i + bin_carry a b i" for i
    using sum_carry_formula sum_digit_formula by simp
  hence "(\<Sum>i<k. (a + b) \<exclamdown> i + 2 * bin_carry a b (i+1)) = (\<Sum>i<k. a \<exclamdown> i + b \<exclamdown> i + bin_carry a b i)"
    using sum.cong by presburger
  hence "(\<Sum>i<k. (a + b) \<exclamdown> i) + 2 * (\<Sum>i<k. bin_carry a b (i+1)) = 
    (\<Sum>i<k. a \<exclamdown> i) + (\<Sum>i<k. b \<exclamdown> i) + (\<Sum>i<k. bin_carry a b i)"
    using sum.distrib sum_distrib_left by (smt (z3) sum.cong)
  hence "count_bits (a+b) + 2 * count_carries a b = count_bits a + count_bits b + count_carries a b"
    using 0 count_bits_def_sum count_carries_def_sum k_def by (metis add.commute add_lessD1)
  thus ?thesis by simp
qed

corollary count_bits_add_le: "count_bits (a+b) \<le> count_bits a + count_bits b"
  using count_carries_count_bits by (metis le_add1)

text \<open>\<open>{@const count_carries}\<close> can be defined in term of \<open>{@const count_bits}\<close>\<close>
corollary count_carries_def_alt: 
  "count_carries a b = count_bits a + count_bits b - count_bits (a+b)"
  using count_carries_count_bits by (metis diff_add_inverse)

lemma count_bits_sum_le: 
  assumes S_fin: "finite S"
  shows "count_bits (sum f S) \<le> (\<Sum>i\<in>S. count_bits (f i))"
proof (induct rule: finite_induct[OF S_fin])
  case 1 show ?case by simp
next 
  case (2 x S) 
  have "count_bits (sum f (insert x S)) = count_bits (f x + sum f S)"
    by (simp add: "2.hyps"(1) "2.hyps"(2))
  also have "... \<le> count_bits (f x) + count_bits (sum f S)"
    using count_bits_add_le by simp
  also have "... \<le> count_bits (f x) + (\<Sum>i\<in>S. count_bits (f i))"
    by (simp add: "2.hyps"(3))
  also have "... = (\<Sum>i\<in>insert x S. count_bits (f i))"
    by (simp add: "2.hyps"(1) "2.hyps"(2))
  finally show ?case .
qed

lemma aux1_carry_set_add_shift:
  "a < 2^k \<Longrightarrow> c < 2^k \<Longrightarrow> i \<le> k \<Longrightarrow> bin_carry (a+b*2^k) (c+d*2^k) i = bin_carry a c i"
proof (induct i)
  case 0 thus ?case unfolding bin_carry_def by simp
next
  case (Suc i)
  have "bin_carry (a+b*2^k) (c+d*2^k) (Suc i) = 
    ((a+b*2^k) \<exclamdown> i + (c+d*2^k) \<exclamdown> i + bin_carry (a+b*2^k) (c+d*2^k) i) div 2"
    using sum_carry_formula by simp
  also have "... = (a \<exclamdown> i + c \<exclamdown> i + bin_carry a c i) div 2"
    using Suc aux2_digit_sum_repr by (simp add: add.commute)
  also have "... = bin_carry a c (Suc i)"
    using sum_carry_formula by simp
  finally show ?case .
qed

lemma aux2_carry_set_add_shift:
  "a < 2^k \<Longrightarrow> c < 2^k \<Longrightarrow> k \<le> i \<Longrightarrow> bin_carry (a+b*2^k) (c+d*2^k) i \<ge> bin_carry b d (i-k)"
proof -
  assume assm1: "a < 2^k" and assm2: "c < 2^k" and i_def: "k \<le> i"
  show ?thesis
  proof (induct rule: nat_induct_at_least[OF i_def])
    case 1 show ?case using bin_carry_def assm1 assm2 by simp
  next
    case (2 i)
    have "bin_carry (a + b * 2 ^ k) (c + d * 2 ^ k) (Suc i) =
      ((a+b*2^k) \<exclamdown> i + (c+d*2^k) \<exclamdown> i + bin_carry (a+b*2^k) (c+d*2^k) i) div 2"
      using sum_carry_formula by simp
    also have "... \<ge> (b \<exclamdown> (i-k) + d \<exclamdown> (i-k) + bin_carry b d (i-k)) div 2"
      using 2 aux1_digit_lt_linear aux_digit_shift assm1 assm2
      by (smt (verit, ccfv_SIG) add.commute add_le_mono div_le_mono le_add_diff_inverse2 order.refl)
    finally show ?case
      using sum_carry_formula 2 by (metis Suc_diff_le Suc_eq_plus1)
  qed
qed

lemma aux3_carry_set_add_shift:
  "a + c < 2^k \<Longrightarrow> k \<le> i \<Longrightarrow> bin_carry (a+b*2^k) (c+d*2^k) i = bin_carry b d (i-k)"
proof -
  assume assm: "a + c < 2^k"
  assume i_def: "k \<le> i"
  show ?thesis
  proof (induct rule: nat_induct_at_least[OF i_def])
    case 1 show ?case using bin_carry_def assm by simp
  next
    case (2 i)
    have "bin_carry (a + b * 2 ^ k) (c + d * 2 ^ k) (Suc i) =
      ((a+b*2^k) \<exclamdown> i + (c+d*2^k) \<exclamdown> i + bin_carry (a+b*2^k) (c+d*2^k) i) div 2"
      using sum_carry_formula by simp
    also have "... = (b \<exclamdown> (i-k) + d \<exclamdown> (i-k) + bin_carry b d (i-k)) div 2"
      using "2" aux1_digit_lt_linear aux_digit_shift assm
      by (smt (verit, best) add.commute add_lessD1 le_add_diff_inverse2)
    also have "... = bin_carry b d (Suc i - k)"
      using sum_carry_formula "2" by (metis Suc_diff_le Suc_eq_plus1)
    finally show ?case .
  qed
qed

lemma carry_set_add_shift:
  "a < 2^k \<Longrightarrow> c < 2^k \<Longrightarrow> carry_set a c \<union> ((+) k) ` carry_set b d \<subseteq> carry_set (a+b*2^k) (c+d*2^k)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?A1 \<union> ?A2 \<subseteq> ?B")
proof -
  assume assm1: "a < 2^k" and assm2: "c < 2^k"
  
  { fix i assume i_def: "i \<in> ?A1"
    have "a + c < 2^(Suc k)"
      using assm1 assm2 by auto
    hence "i \<le> k" 
      using i_def carry_set_subset_variant by fastforce
    hence "i \<in> ?B" 
      using carry_set_def i_def aux1_carry_set_add_shift[OF assm1 assm2] by auto }
  note 0 = this  
  
  { fix i assume i_def: "i \<in> ?A2" 
    hence "k \<le> i" 
      by auto
    hence "i \<in> ?B" 
      using i_def aux2_carry_set_add_shift[OF assm1 assm2] unfolding carry_set_def
      by (smt (verit) add_diff_cancel_left' carry_bounded image_iff linorder_not_less 
          mem_Collect_eq nat_less_le) }
  note 1 = this

  from 0 1 show ?thesis by auto
qed

corollary count_carries_add_shift:
  "a < 2^k \<Longrightarrow> c < 2^k \<Longrightarrow> count_carries (a + b*2^k) (c + d*2^k) 
                        \<ge> count_carries a c + count_carries b d"
proof -
  assume assm1: "a < 2^k" and assm2: "c < 2^k"
  have "carry_set a c \<inter> ((+) k) ` carry_set b d = {}"
  proof -
    { fix i assume i_def: "i \<in> carry_set a c \<inter> ((+) k) ` carry_set b d"
      have "a + c < 2^(Suc k)" 
        using assm1 assm2 by auto
      hence "i < Suc k \<and> i \<ge> k"
        using carry_set_subset_variant i_def by fastforce 
      hence "i = k" 
        by auto
      moreover have "0 \<notin> carry_set b d"
        unfolding carry_set_def bin_carry_def by simp
      ultimately have "False" 
        using i_def by auto }
    thus ?thesis by auto
  qed
  hence "card (carry_set a c \<union> ((+) k) ` carry_set b d) = 
    card (carry_set a c) + card (carry_set b d)"
    by (metis card_Un_disjoint card_image carry_set_finite finite_imageI inj_on_add)
  thus ?thesis 
    unfolding count_carries_def using carry_set_add_shift[OF assm1 assm2]
    by (metis card_mono carry_set_finite)
qed

lemma carry_set_add_shift_no_overflow:
  "a + c < 2^k \<Longrightarrow> carry_set (a+b*2^k) (c+d*2^k) = carry_set a c \<union> ((+) k) ` carry_set b d"
  (is "_ \<Longrightarrow> ?A = ?B")
proof
  assume assm: "a + c < 2^k" show "?A \<subseteq> ?B"
  proof 
    fix i assume i_def: "i \<in> ?A" 
    { assume "i < k" 
      hence "bin_carry a c i = 1"
        using aux1_carry_set_add_shift assm i_def carry_set_def by simp
      hence "i \<in> carry_set a c"
        using carry_set_def by simp }
    note 0 = this
    { assume "i \<ge> k" 
      hence "bin_carry b d (i-k) = 1"
        using aux3_carry_set_add_shift[OF assm] i_def carry_set_def by simp
      hence "i \<in> ((+) k) ` carry_set b d"
        using carry_set_def \<open>k \<le> i\<close> image_iff by fastforce }
    note 1 = this
    from 0 1 show "i \<in> ?B" by force
  qed
next
  assume "a + c < 2^k" thus "?B \<subseteq> ?A"
    using carry_set_add_shift
    by (meson add_lessD1 linorder_not_less trans_le_add2)
qed 

corollary count_carries_add_shift_no_overflow:
  "a + c < 2^k \<Longrightarrow> count_carries (a + b*2^k) (c + d*2^k) = count_carries a c + count_carries b d"
proof -
  assume assm: "a + c < 2^k"
  have "carry_set a c \<inter> ((+) k) ` carry_set b d = {}"
  proof -
    { fix i assume "i \<in> carry_set a c \<inter> ((+) k) ` carry_set b d"
      hence "i < k \<and> i \<ge> k"
        using carry_set_subset_variant[OF assm] by auto }
    thus ?thesis by auto
  qed
  thus ?thesis 
    unfolding count_carries_def carry_set_add_shift_no_overflow[OF assm]
    by (simp add: card_Un_disjoint card_image carry_set_finite)
qed

corollary count_carries_even_even: "count_carries (2*a) (2*b) = count_carries a b"
  using count_carries_add_shift_no_overflow[of "0" "0" "1" "a" "b"] by (simp add: mult.commute)

lemma count_carries_digitwise:
  assumes "1 \<le> k" and "\<forall>i<q. f i < 2^k \<and> g i < 2^k"
  shows "count_carries (\<Sum>i<q. f i * (2^k)^i) (\<Sum>i<q. g i * (2^k)^i) \<ge> 
    (\<Sum>i<q. count_carries (f i) (g i))"
using assms
proof (induct q)
  case 0 thus ?case by auto
next
  case (Suc q) 
  have 0:"1 < (2::nat)^k" 
    using Suc.prems(1) dual_order.strict_trans2 less_exp by blast
  have bound: "(\<Sum>i<q. f i * (2^k)^i) < 2^(k*q) \<and> (\<Sum>i<q. g i * (2^k)^i) < 2^(k*q)"
    using aux_digit_sum_bound[OF 0] Suc.prems(2) power_mult by (metis (full_types) less_Suc_eq)
  
  have "count_carries (\<Sum>i<q. f i * (2^k)^i) (\<Sum>i<q. g i * (2^k)^i) \<ge>
    (\<Sum>i<q. count_carries (f i) (g i))"
    using Suc less_Suc_eq by presburger
  hence "(\<Sum>i<Suc q. count_carries (f i) (g i)) \<le>
    count_carries (\<Sum>i<q. f i * (2^k)^i) (\<Sum>i<q. g i * (2^k)^i) + count_carries (f q) (g q)"
    by simp
  also have "... \<le> count_carries ((\<Sum>i<q. f i * (2^k)^i) + f q * 2^(k*q)) ((\<Sum>i<q. g i * (2^k)^i) + g q * 2^(k*q))"
    using bound count_carries_add_shift by simp
  also have "... = count_carries (\<Sum>i<Suc q. f i * (2^k)^i) (\<Sum>i<Suc q. g i * (2^k)^i)"
    using power_mult by (smt (verit, del_insts) mult.commute sum.lessThan_Suc)
  finally show ?case .
qed

corollary count_carries_digitwise_specific:
  assumes "1 \<le> k" and "\<forall>i<q. f i < 2^k \<and> g i < 2^k"
  shows "i < q \<Longrightarrow> count_carries (\<Sum>i<q. f i * (2^k)^i) (\<Sum>i<q. g i * (2^k)^i) \<ge> 
    count_carries (f i) (g i)"
proof -
  assume "i < q" 
  hence "count_carries (f i) (g i) \<le> (\<Sum>i<q. count_carries (f i) (g i))"
    using member_le_sum by (metis (no_types, lifting) finite_lessThan lessThan_iff zero_le)
  thus ?thesis
    using count_carries_digitwise[OF assms(1) assms(2)] by auto
qed

lemma count_carries_digitwise_no_overflow:
  assumes "k \<ge> 1" and "\<forall>i<q. f i + g i < 2^k"
  shows "count_carries (\<Sum>i<q. f i * (2^k)^i) (\<Sum>i<q. g i * (2^k)^i) = 
    (\<Sum>i<q. count_carries (f i) (g i))"
using assms
proof (induct q)
  case 0 thus ?case by auto
next
  case (Suc q) 
  have bound: "(\<Sum>i<q. f i * (2^k)^i) + (\<Sum>i<q. g i * (2^k)^i) < 2^(k*q)"
  proof -
    have 0: "1 < (2::nat)^k" 
      using Suc.prems(1) dual_order.strict_trans2 less_exp by blast
 
    have "(\<Sum>i<q. f i * (2^k)^i) + (\<Sum>i<q. g i * (2^k)^i) = (\<Sum>i<q. (f i + g i) * (2^k)^i)"
      by (simp add: sum.distrib algebra_simps)
    also have "... < (2^k)^q"
      using aux_digit_sum_bound[OF 0] Suc.prems(2) less_Suc_eq by presburger
    finally show ?thesis 
      unfolding power_mult .
  qed

  have "(\<Sum>i<Suc q. count_carries (f i) (g i)) =
    count_carries (\<Sum>i<q. f i * (2^k)^i) (\<Sum>i<q. g i * (2^k)^i) + count_carries (f q) (g q)"
    using Suc by simp
  also have "... = count_carries ((\<Sum>i<q. f i * (2^k)^i) + f q * 2^(k*q)) 
    ((\<Sum>i<q. g i * (2^k)^i) + g q * 2^(k*q))"
    using bound count_carries_add_shift_no_overflow assms by auto
  also have "... = count_carries (\<Sum>i<Suc q. f i * (2^k)^i) (\<Sum>i<Suc q. g i * (2^k)^i)"
    using power_mult by (smt (verit, del_insts) mult.commute sum.lessThan_Suc)
  finally show ?case 
    by simp
qed

lemma carry_set_empty_iff:
  "carry_set a b = {} \<longleftrightarrow> (\<forall>i. a \<exclamdown> i + b \<exclamdown> i \<le> 1)"
proof
  assume "carry_set a b = {}"
  hence "bin_carry a b i = 0" for i
    unfolding carry_set_def using carry_bounded
    by (smt (verit) Collect_empty_eq_bot div_le_dividend div_self empty_def nle_le)
  hence "(a \<exclamdown> i + b \<exclamdown> i) div 2 = 0" for i
    using sum_carry_formula by (metis add.right_neutral)
  thus "\<forall>i. a \<exclamdown> i + b \<exclamdown> i \<le> 1"
    by (metis Suc_1 add_self_div_2 div_le_mono nat_1_add_1 not_less_eq_eq not_one_le_zero)
next 
  assume assm: "\<forall>i. a \<exclamdown> i + b \<exclamdown> i \<le> 1"
  hence "bin_carry a b k = 0" for k
    using carry_digit_impl by (metis Suc_1 Suc_n_not_le_n)  
  thus "carry_set a b = {}"
    unfolding carry_set_def by simp
qed

corollary count_carries_zero_iff:
  "count_carries a b = 0 \<longleftrightarrow> (\<forall>i. a \<exclamdown> i + b \<exclamdown> i \<le> 1)"
  using count_carries_def carry_set_empty_iff by (simp add: carry_set_finite)

lemma no_carry_no_overflow:
  assumes "a < 2^k" and "b < 2^k" and "count_carries a b = 0"
  shows "a + b < 2^k"
proof -
  have "carry_set a b = {}"
    using assms(3) count_carries_def carry_set_finite by simp
  hence "bin_carry a b i = 0" for i
    unfolding carry_set_def using carry_bounded
    by (smt (verit) Collect_empty_eq_bot div_le_dividend div_self empty_def nle_le)
  hence "(a mod 2^k + b mod 2^k) div 2^k = 0"
    using bin_carry_def by simp
  hence "(a + b) div 2^k = 0"
    using assms(1-2) by simp
  thus "a + b < 2^k"
    by (simp add: div_eq_0_iff)
qed

lemma count_carries_divisibility_pow2: "count_carries (2^k-1) x = 0 \<longleftrightarrow> 2^k dvd x"
proof 
  assume "count_carries (2^k-1) x = 0"
  hence "((2^k-1) \<exclamdown> i) + (x \<exclamdown> i) \<le> 1" for i
    using count_carries_zero_iff by simp
  hence "i < k \<Longrightarrow> x \<exclamdown> i = 0" for i
    by (metis add_le_same_cancel2 bot_nat_0.extremum even_decr_exp_div_exp_iff' 
        le_antisym mod2_eq_if not_less nth_bit_def)
  thus "2^k dvd x" using aux2_digit_wise_equiv by presburger
next
  assume assm: "2^k dvd x"
  { fix i assume "i < k"
    hence "2 * 2^i dvd x"
      by (metis Suc_leI assm dvd_trans le_imp_power_dvd power_Suc)
    hence "x \<exclamdown> i = 0"
      unfolding nth_bit_def by auto }
  hence "((2^k-1) \<exclamdown> i) + (x \<exclamdown> i) \<le> 1" for i
    using nth_bit_bounded
    by (metis Nat.le_diff_conv2 add.right_neutral bot_nat_0.extremum even_decr_exp_div_exp_iff' 
        mod_eq_0_iff_dvd not_less nth_bit_def)
  thus "count_carries (2^k-1) x = 0"
    using count_carries_zero_iff by simp
qed

lemma nth_digit_gen_power_series_general:
  assumes "1 < b" and "\<forall>k\<le>q. f k < b"
  shows "nth_digit (\<Sum>k=0..q. f k * b^k) i b = (if i \<le> q then f i else 0)"
  (is "nth_digit ?X _ _ = _")
proof (cases "i \<le> q") 
  case False
  have "?X < b^(Suc q)"
    using aux_digit_sum_bound[OF assms(1)] assms(2)
    by (metis (full_types) Suc_leI atLeast0AtMost lessThan_Suc_atMost verit_comp_simplify1(3))
  thus ?thesis 
    using False unfolding nth_digit_def
    by (metis (no_types, lifting) assms(1) div_less dual_order.strict_trans2 
        linordered_nonzero_semiring_class.zero_le_one mod_less not_less_eq_eq power_increasing_iff 
        verit_comp_simplify1(3))
next
  case True

  have split0: "?X = (\<Sum>k<i+1. f k * b^k) + (\<Sum>k<q-i. f (k+i+1) * b^k) * b^(i+1)"
  proof -
    have "(\<Sum>k=i+1..q. f k * b^k) = (\<Sum>k=Suc i..<Suc q. f k * b^k)"
      using Suc_eq_plus1 atLeastLessThanSuc_atLeastAtMost by presburger 
    also have "... = (\<Sum>k=0 + Suc i..<(Suc q - Suc i) + Suc i. f k * b^k)"
      by (simp add: True)
    also have "... = (\<Sum>k=0..<(Suc q - Suc i). f (k + Suc i) * b^(k + Suc i))"
      using sum.shift_bounds_nat_ivl by blast
    also have "... = (\<Sum>k<q-i. f (k+i+1) * b^(k+i+1))"
      using atLeast0LessThan by force
    also have "... = (\<Sum>k<q-i. f (k+i+1) * b^k * b^(i+1))"
      by (simp add: power_add algebra_simps)
    finally have rewrite: "(\<Sum>k=i+1..q. f k * b^k) = (\<Sum>k<q-i. f (k+i+1) * b^k) * b^(i+1)"
      using sum_distrib_right by (smt (verit) sum.cong)

    have "?X = (\<Sum>k=0..i. f k * b^k) + (\<Sum>k=i+1..q. f k * b^k)"
      using sum.ub_add_nat
      by (smt (verit, ccfv_threshold) True bot_nat_0.extremum nat_le_iff_add)
    thus ?thesis 
      using rewrite by (metis Suc_eq_plus1 atLeast0AtMost lessThan_Suc_atMost)
  qed
  have bound0: "(\<Sum>k<i+1. f k * b^k) < b^(i+1)"
    using aux_digit_sum_bound[OF assms(1)] assms(2) True
    using Suc_eq_plus1 le_trans less_Suc_eq_le by presburger
  have 0: "nth_digit ?X i b = nth_digit (\<Sum>k<i+1. f k * b^k) i b" 
    (is "_ = nth_digit ?Y _ _")
    using aux2_digit_gen_sum_repr[OF bound0] unfolding split0
    by (metis (no_types, lifting) add.commute less_add_same_cancel1 zero_less_one) 
  
  have split1: "?Y = (\<Sum>k<i. f k * b^k) + f i * b^i"
    by simp
  have bound1: "(\<Sum>k<i. f k * b^k) < b^i" 
    using aux_digit_sum_bound[OF assms(1)] assms(2) True by auto
  have 1: "nth_digit ?Y i b = nth_digit (f i * b^i) i b"
    using aux3_digit_gen_sum_repr[OF bound1 assms(1)] unfolding split1
    by (simp add: add.commute)

  have 2: "nth_digit (f i * b^i) i b = f i"
    unfolding nth_digit_def using assms(2) True by auto

  show ?thesis
    using 0 1 2 True by simp
qed


lemma aux_count_bits_multiplicity:
  "count_bits (Suc x) + multiplicity 2 (Suc x) = count_bits x + 1"
proof (induct x rule: Bit_Operations.nat_bit_induct)
  case zero thus ?case using count_bits_1 by auto
next
  case (even x)
  have "\<not> 2 dvd Suc (2*x)"
    by simp
  thus ?case 
    using count_bits_even count_bits_odd by (simp add: multiplicity_eq_zero_iff) 
next
  case (odd x)
  have "multiplicity 2 (2 * Suc x) = multiplicity 2 (Suc x) + 1"
    by (metis Suc_1 Suc_eq_plus1 multiplicity_times_same nat.simps(3) odd_one)
  thus ?case
    using count_bits_even count_bits_odd
    by (metis add.commute add_2_eq_Suc add_Suc_right mult_Suc_right odd plus_1_eq_Suc)
qed

lemma count_bits_multiplicity: 
  "count_bits x = multiplicity 2 (2*x choose x)"
proof (induct x)
  case 0
  then show ?case
    using One_nat_def binomial_n_0 multiplicity_one_nat count_bits_0 by presburger
next
  case (Suc x)
  
  have p: "prime_elem (2::nat)"
    using prime_elem_nat_iff two_is_prime_nat by presburger 
  have e: "(2 * Suc x choose Suc x) * Suc x * Suc x = (2*x choose x) * 2 * Suc x * (2*x+1)"
    by (smt (z3) Suc_times_binomial_add add.right_neutral add_2_eq_Suc add_Suc_right 
        add_diff_cancel_left' binomial_absorption mult.commute mult.left_commute mult_2 
        mult_Suc_right plus_1_eq_Suc)
  
  let ?m = "multiplicity (2::nat)"

  have "\<not> (2 dvd (2*x+1))" by simp
  hence "?m ((2 * Suc x choose Suc x) * Suc x * Suc x) = ?m ((2*x choose x) * 2 * (Suc x))"
    by (metis (no_types, lifting) e mult.commute multiplicity_prime_elem_times_other p)
  hence "?m ((2 * Suc x choose Suc x) * Suc x) = ?m ((2*x choose x) * 2)"
    using prime_elem_multiplicity_mult_distrib[OF p]
    by (metis add_is_0 add_right_cancel e mult_is_0 nat.simps(3) zero_neq_one)    
  hence "?m (2 * Suc x choose Suc x) + ?m (Suc x) = ?m (2*x choose x) + ?m 2"
    using prime_elem_multiplicity_mult_distrib[OF p] binomial_eq_0_iff
    by (metis less_numeral_extra(3) mult_2 nat.simps(3) nat_zero_less_power_iff not_add_less1 
        zero_power2)
  hence "?m (2 * Suc x choose Suc x) + ?m (Suc x) = count_bits x + 1"
    using multiplicity_prime[OF p] Suc by metis
  hence "?m (2 * Suc x choose Suc x) = count_bits (Suc x)"
    using aux_count_bits_multiplicity by (metis add_diff_cancel_right')
  thus ?case by simp
qed

corollary count_bits_divibility_binomial:
  "2^k dvd (2*x choose x) \<longleftrightarrow> k \<le> count_bits x"
  using count_bits_multiplicity by (simp add: power_dvd_iff_le_multiplicity)  


end