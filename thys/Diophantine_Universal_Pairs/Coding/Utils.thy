theory Utils
  imports Main
begin

definition is_square::"int\<Rightarrow>bool" where
  "is_square n = (\<exists>k. n = k^2)"

definition is_power2::"int\<Rightarrow>bool" where
  "is_power2 x \<equiv> (\<exists>n::nat. x = 2^n)"

lemma is_power2_ge1: "is_power2 x \<Longrightarrow> 1 \<le> x"
  unfolding is_power2_def by force

lemma is_power2_mult[simp]: "is_power2 x \<Longrightarrow> is_power2 y \<Longrightarrow> is_power2 (x * y)"
  unfolding is_power2_def by (metis power_add)

lemma is_power2_pow[simp]: "is_power2 x \<Longrightarrow> is_power2 (x^n)"
  unfolding is_power2_def by (metis power_mult)

lemma is_power2_1[simp]: "is_power2 1" 
  unfolding is_power2_def by (metis power_0)
lemma is_power2_2[simp]: "is_power2 2" 
  unfolding is_power2_def by (metis power_one_right)
lemma is_power2_4[simp]: "is_power2 4" 
  unfolding is_power2_def by (metis mult_2_right numeral_Bit0 power2_eq_square)


lemma is_power2_div2: "is_power2 x \<Longrightarrow> 2 \<le> x \<Longrightarrow> is_power2 (x div 2)"
  unfolding is_power2_def
  by (smt (verit, ccfv_threshold) bot_nat_0.not_eq_extremum int_power_div_base power_0)

lemma digit_repr_lt:
  fixes q :: nat
  fixes b :: int
  assumes "b > 1"
  assumes "\<forall>k. f k < b"
  shows "(\<Sum>k = 0..q. f k * b ^ k) < b^(Suc q)"
proof (induct q)
  case 0
  then show ?case using assms(2) by auto
next
  case (Suc q)
  have le_bound: "f k \<le> b - 1" for k
    using assms(2) by auto
  have "(\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q) 
      \<le> (\<Sum>k = 0..q. f k * b ^ k) + (b-1) * (b * b ^ q)" using le_bound assms(1) by force
  also have "... < b^(Suc q) + (b-1) * (b * b ^ q)" using Suc by auto
  also have "... \<le> b * b * b^q"
    by simp (metis (mono_tags, opaque_lifting) add.commute diff_add_cancel distrib_left
                    linorder_not_less mult.left_commute mult.right_neutral order_less_imp_le)
  finally show ?case using Suc by auto
qed 

end
