subsection \<open>Preliminary commutation relations\<close>

theory CommutationRelations
  imports RegisterMachineSimulation MachineEquations
begin

lemma aux_commute_bitAND_sum:
  fixes N C :: nat
    and fxt :: "nat \<Rightarrow> nat"
  shows "\<forall>i\<le>N. \<forall>j\<le>N. i \<noteq> j \<longrightarrow> (\<forall>k. (fct i) \<exclamdown> k * (fct j) \<exclamdown> k = 0)
          \<Longrightarrow> (\<Sum>k \<le> N. fct k && C) = (\<Sum>k \<le> N. fct k) && C"
proof (induct N)
  case 0
  then show ?case by auto
next
  case (Suc N)
  assume Suc_assms: "\<forall>i\<le>Suc N. \<forall>j\<le>Suc N. i \<noteq> j \<longrightarrow> (\<forall>k. fct i \<exclamdown> k * fct j \<exclamdown> k = 0)"

  have "(\<Sum>k\<le>Suc N. fct k && C) = (\<Sum>k\<le>N. fct k && C) + (fct (Suc N) && C)"
    by (auto cong: sum.cong) 
  also have "... = (sum fct {..N} && C) + (fct (Suc N) && C)"
    using Suc by auto
  also have "... = (sum fct {..N} + fct (Suc N)) && C"
  proof -
    let ?a = "sum fct {..N} && C"
    let ?b = "fct (Suc N) && C"

    have formula: "\<forall>d. ( ?a + ?b ) \<exclamdown> d = ( ?a \<exclamdown> d + ?b \<exclamdown> d + bin_carry ?a ?b d ) mod 2"
      using sum_digit_formula by auto


    (* mutual proof of both statements, they are interdependent in the inductive step *)
    have nocarry4: "\<forall>n\<le>Suc N. \<forall>d. (sum fct {..n} \<exclamdown> d > 0 \<longrightarrow> (\<exists>i\<le>n. (fct i) \<exclamdown> d > 0))
                        \<and> bin_carry (sum fct {..<n}) (fct n) d = 0"
    proof -
      {
        fix n

        (* contrapositive of first statement*)
        have "n \<le> Suc N \<Longrightarrow>
                \<forall>d. ((\<forall>i\<le>n. (fct i) \<exclamdown> d = 0)
                \<longrightarrow> sum fct {..n} \<exclamdown> d = 0) \<and> bin_carry (sum fct {..<n}) (fct n) d = 0" 
        proof (induction n)
          case 0
          then show ?case by (simp add: bin_carry_def)
        next
          case (Suc m)
          (* using IH of first statement, obtain helper result *)
          from Suc Suc.prems have ex: "\<forall>d. sum fct {..<Suc m} \<exclamdown> d > 0 \<longrightarrow> (\<exists>i<Suc m. fct i \<exclamdown> d = 1)"
            using nth_bit_def
            by (metis One_nat_def Suc_less_eq lessThan_Suc_atMost less_Suc_eq nat_less_le
                      not_mod2_eq_Suc_0_eq_0)

          (* then show another helper result ... *)
          have h1: "\<forall>d. sum fct {..<Suc m} \<exclamdown> d + fct (Suc m) \<exclamdown> d \<le> 1"
          proof -
            {
              fix d
              have "sum fct {..<Suc m} \<exclamdown> d + fct (Suc m) \<exclamdown> d \<le> 1"
              proof (cases "sum fct {..<Suc m} \<exclamdown> d = 0")
                case True
                have "fct (Suc m) \<exclamdown> d \<le> 1"
                  using nth_bit_def by auto
                then show ?thesis using True by auto
              next
                case False
                then have "\<exists>i<Suc m. fct i \<exclamdown> d > 0"
                  using ex by (metis neq0_conv zero_less_one)
                then obtain i where i: "i<Suc m \<and> fct i \<exclamdown> d > 0" by auto 
                hence "i \<le> Suc N" using Suc.prems by auto
                hence "\<forall>j\<le>Suc N. i \<noteq> j \<longrightarrow> (\<forall>k. fct i \<exclamdown> k * fct j \<exclamdown> k = 0)"
                  using Suc_assms by auto
                then have "fct (Suc m) \<exclamdown> d = 0"
                  using Suc.prems i nat_neq_iff
                  by (auto) (blast)
                moreover from False have "sum fct {..<Suc m} \<exclamdown> d = 1"
                  by (simp add: nth_bit_def)
                ultimately show ?thesis by auto
              qed
            }
            thus ?thesis by auto
          qed

          (* ... in order to show the inductive step of the second statement *)
          from h1 have h2: "\<forall>d. bin_carry (sum fct {..<Suc m}) (fct (Suc m)) d = 0"
            using carry_digit_impl by (metis Suc_1 Suc_n_not_le_n)
          then have nocarry3: "\<forall>d. bin_carry (sum fct {..m}) (fct (Suc m)) d = 0"
            by (simp add: lessThan_Suc_atMost)

          (* finally use the just proven inductive step for the 2nd statement to show the
              inductive step for the first statement *)
          {
            fix d
            assume a: "\<forall>i\<le>Suc m. (fct i) \<exclamdown> d = 0"
            have "sum fct {..Suc m} \<exclamdown> d = (sum fct {..m} + fct (Suc m)) \<exclamdown> d"
              by auto
            also have "... =
              (sum fct {..m} \<exclamdown> d + fct (Suc m) \<exclamdown> d + bin_carry (sum fct {..m}) (fct (Suc m)) d) mod 2"
              using sum_digit_formula[of "sum fct {..m}" "fct (Suc m)" "d"] by auto
            finally have "sum fct {..Suc m} \<exclamdown> d = 0"
              using nocarry3 Suc a by auto
          }
          with h2 show ?case by auto
        qed

        then have "n \<le> Suc N \<Longrightarrow> \<forall>d. (sum fct {..n} \<exclamdown> d > 0 \<longrightarrow> (\<exists>i\<le>n. (fct i) \<exclamdown> d > 0))
                      \<and> bin_carry (sum fct {..<n}) (fct n) d = 0"
          by auto
      }
      thus ?thesis by auto
    qed

    from Suc_assms have h3: "\<forall>d. ?a \<exclamdown> d + ?b \<exclamdown> d \<le> 1"
    proof -
      have "\<forall>d. ?a \<exclamdown> d + ?b \<exclamdown> d = (sum fct {..N} \<exclamdown> d + fct (Suc N) \<exclamdown> d) * C \<exclamdown> d"
        using bitAND_digit_mult add_mult_distrib by auto
      then have "\<forall>d. ?a \<exclamdown> d + ?b \<exclamdown> d \<le> (sum fct {..N} \<exclamdown> d + fct (Suc N) \<exclamdown> d)"
        using nth_bit_def by auto
      thus ?thesis
        using sum_carry_formula nocarry4 no_carry_mult_equiv nth_bit_bounded bitAND_digit_mult
        by (metis One_nat_def add.commute add_decreasing le_Suc_eq lessThan_Suc_atMost
                  nat_1_eq_mult_iff)
    qed
    from h3 have h4: "\<forall>d. bin_carry ?a ?b d = 0"
      by (metis Suc_1 Suc_n_not_le_n carry_digit_impl)

    (* Helper for proof chain below *)
    have h5: "\<forall>d. bin_carry (sum fct {..N}) (fct (Suc N)) d = 0"
      using nocarry4 lessThan_Suc_atMost by auto

    from formula h3 h4 have "\<forall>d. ( ?a + ?b ) \<exclamdown> d = ?a \<exclamdown> d + ?b \<exclamdown> d"
      by (metis (no_types, lifting) add_cancel_right_left add_le_same_cancel1 add_self_mod_2
            le_zero_eq not_mod2_eq_Suc_0_eq_0 nth_bit_def one_mod_two_eq_one plus_1_eq_Suc)

    then have "\<forall>d. ( ?a + ?b ) \<exclamdown> d = sum fct {..N} \<exclamdown> d * C \<exclamdown> d + fct (Suc N) \<exclamdown> d * C \<exclamdown> d"
      using bitAND_digit_mult by auto

    then have "\<forall>d. ( ?a + ?b ) \<exclamdown> d = (sum fct {..N} \<exclamdown> d + fct (Suc N) \<exclamdown> d) * C \<exclamdown> d"
      by (simp add: add_mult_distrib)
    moreover have "\<forall>d. sum fct {..N} \<exclamdown> d + fct (Suc N) \<exclamdown> d
      = ( sum fct {..N} \<exclamdown> d + fct (Suc N) \<exclamdown> d + bin_carry (sum fct {..N}) (fct (Suc N)) d ) mod 2"
      using h5 sum_carry_formula
      by (metis add_diff_cancel_left' add_diff_cancel_right' mult_div_mod_eq mult_is_0)
    ultimately have "\<forall>d. ( ?a + ?b ) \<exclamdown> d = (sum fct {..N} + fct (Suc N)) \<exclamdown> d * C \<exclamdown> d"
      using sum_digit_formula by auto

    then have "\<forall>d. ( ?a + ?b ) \<exclamdown> d = ( (sum fct {..N} + fct (Suc N)) && C ) \<exclamdown> d"
      using bitAND_digit_mult by auto
    thus ?thesis using digit_wise_equiv by blast
  qed
  ultimately show ?case by auto
qed


lemma aux_commute_bitAND_sum_if:
  fixes N const :: nat
  assumes nocarry: "\<forall>i\<le>N. \<forall>j\<le>N. i \<noteq> j \<longrightarrow> (\<forall>k. (fct i) \<exclamdown> k * (fct j) \<exclamdown> k = 0)"
  shows "(\<Sum>k \<le> N. if cond k then fct k && const else 0)
       = (\<Sum>k \<le> N. if cond k then fct k else 0) && const"
proof -
  from nocarry have nocarry_if:
    "\<forall>i\<le>N. \<forall>j\<le>N. i \<noteq> j \<longrightarrow> (\<forall>k. (if cond i then fct i else 0) \<exclamdown> k *  (if cond j then fct j else 0) \<exclamdown> k = 0)"
    by (metis (full_types) aux1_digit_wise_equiv mult.commute mult_zero_left)

  have "(if cond k then fct k && const else 0) = (if cond k then fct k else 0) && const" for k 
    by auto
  hence "(\<Sum>k \<le> N. if cond k then fct k && const else 0)
          = (\<Sum>k \<le> N. (if cond k then fct k else 0) && const)"
    by auto
  also have "... = (\<Sum>k \<le> N. if cond k then fct k else 0) && const"
    using nocarry_if aux_commute_bitAND_sum[where ?fct = "\<lambda>k. (if cond k then fct k else 0)"]
    by blast
  ultimately show ?thesis by auto
qed

lemma mod_mod:
  fixes x a b :: nat
  shows "x mod 2^a mod 2^b = x mod 2^(min a b)"
  by (metis min.commute take_bit_eq_mod take_bit_take_bit)

lemma carry_gen_pow2_reduct: 
  assumes "c>0"
  defines b: "b \<equiv> 2 ^ (Suc c)"
  assumes "nth_digit x (t-1) (2^Suc c) \<exclamdown> c = 0" 
      and "nth_digit y (t-1) (2^Suc c) \<exclamdown> c = 0" 
    shows "k\<le>c \<Longrightarrow> bin_carry (nth_digit x t b) (nth_digit y t b) k 
                 = bin_carry x y (Suc c * t + k)"
proof (induction k)
  case 0
  then show ?case
  proof (cases "t=0")
    case True
    then show ?thesis using bin_carry_def by auto
  next
    case False
    hence "t>0" by auto
    from assms(3) have "x \<exclamdown> (Suc c * (t - 1) + c) = 0"
      using digit_gen_pow2_reduct[of "c" "Suc c" "x" "t-1"] by auto
    moreover have "y \<exclamdown> (Suc c * (t - 1) + c) = 0" 
      using assms(4) digit_gen_pow2_reduct[of "c" "Suc c" "y" "t-1"] by auto
    moreover have "Suc c * (t - 1) + c = t + c * t - Suc 0" 
      using add.left_commute gr0_conv_Suc \<open>t>0\<close> by auto
    ultimately have "(x \<exclamdown> (t + c * t - Suc 0) + y \<exclamdown> (t + c * t - Suc 0) 
      + bin_carry x y (t + c * t - Suc 0)) \<le> 1" using carry_bounded by auto 
    hence "bin_carry x y (Suc c * t) = 0"
      using sum_carry_formula[of "x" "y" "Suc c * t - 1"] \<open>c>0\<close> \<open>t>0\<close> by auto
  
    moreover have "bin_carry (nth_digit x t b) (nth_digit y t b) 0 = 0" 
      using 0 bin_carry_def by auto
    ultimately show ?thesis by auto
  qed
next
  case (Suc k)
  have "k<Suc c \<Longrightarrow> x \<exclamdown> (Suc c * t + k) = nth_digit x t b \<exclamdown> k" 
    using digit_gen_pow2_reduct[of "k" "Suc c" "x" "t"] b by auto
  moreover have "k<Suc c \<Longrightarrow> y \<exclamdown> (Suc c * t + k) = nth_digit y t b \<exclamdown> k"
    using digit_gen_pow2_reduct[of "k" "Suc c" "y" "t"] b by auto
  ultimately show ?case using Suc 
      sum_carry_formula[of "nth_digit x t b" "nth_digit y t b" "k"] 
      sum_carry_formula[of "x" "y" "Suc c * t + k"]
      by auto
qed

lemma nth_digit_bound:
  fixes c defines "b \<equiv> 2 ^ (Suc c)"
  shows "nth_digit x t b < 2 ^ (Suc c)"
  using nth_digit_def b_def by auto

lemma digit_wise_block_additivity:
  fixes c
  defines "b \<equiv> 2 ^ Suc c" 
  assumes "nth_digit x (t-1) (2^Suc c) \<exclamdown> c = 0" 
      and "nth_digit y (t-1) (2^Suc c) \<exclamdown> c = 0" 
      and "k\<le>c"
      and "c>0"
  shows "nth_digit (x+y) t b \<exclamdown> k = (nth_digit x t b + nth_digit y t b) \<exclamdown> k"
proof - 
  have "k < Suc c" using `k\<le>c` by simp
  have x: "nth_digit x t b \<exclamdown> k = x \<exclamdown> (Suc c * t + k)"
    using digit_gen_pow2_reduct[of "k" "Suc c" "x" "t"] b_def `k<Suc c` by auto
  have y: "nth_digit y t b \<exclamdown> k = y \<exclamdown> (Suc c * t + k)" 
    using digit_gen_pow2_reduct[of "k" "Suc c" "y" "t"] b_def `k<Suc c` by auto

  have "(nth_digit x t b + nth_digit y t b) \<exclamdown> k 
      = ((nth_digit x t b) \<exclamdown> k + (nth_digit y t b) \<exclamdown> k 
      + bin_carry (nth_digit x t b) (nth_digit y t b) k) mod 2" 
    using sum_digit_formula[of "nth_digit x t b" "nth_digit y t b" "k"] by auto  
  also have "... = (x \<exclamdown> (Suc c * t + k) + y \<exclamdown> (Suc c * t + k) 
      + bin_carry (nth_digit x t b) (nth_digit y t b) k) mod 2" 
    using x y by auto 
  also have "... = (x \<exclamdown> (Suc c * t + k) + y \<exclamdown> (Suc c * t + k) 
      + bin_carry x y (Suc c * t + k)) mod 2" 
    using carry_gen_pow2_reduct[of "c" "x" "t" "y" "k"] assms by auto
  also have "... = (x + y) \<exclamdown> (Suc c * t + k)" 
    using sum_digit_formula by auto
  also have "... = nth_digit (x+y) t b \<exclamdown> k"
    using digit_gen_pow2_reduct[of "k" "Suc c" "x+y" "t"] b_def `k<Suc c` by auto
  finally show ?thesis by auto
qed

lemma block_additivity:
  assumes "c > 0"
  defines "b \<equiv> 2 ^ Suc c"
  assumes "nth_digit x (t-1) b \<exclamdown> c = 0" 
      and "nth_digit y (t-1) b \<exclamdown> c = 0"
      and "nth_digit x t b \<exclamdown> c = 0" 
      and "nth_digit y t b \<exclamdown> c = 0"
      (* needs stronger assumptions than digit_wise_block_additivity *)
  shows "nth_digit (x+y) t b = nth_digit x t b + nth_digit y t b"
proof -
  {
    have "nth_digit x t b < b" using nth_digit_bound b_def by auto 
    hence x_digit_bound: "\<And>k. k\<ge>Suc c \<longrightarrow> nth_digit x t b \<exclamdown> k = 0"
      using nth_bit_def b_def aux_lt_implies_mask b_def by metis 
  
    have "nth_digit y t b < b" using nth_digit_bound b_def by auto 
    hence y_digit_bound: "\<And>k. k\<ge>Suc c \<longrightarrow> nth_digit y t b \<exclamdown> k = 0"
      using nth_bit_def b_def aux_lt_implies_mask b_def by metis 

    fix k
    assume k: "k\<ge>Suc c"
    have carry0: "bin_carry (nth_digit x t b) (nth_digit y t b) k = 0"
    proof - (* induction proof using rule nat_induct_at_least to accommodate fact k *)
      (* base case *)
      have base: "bin_carry (nth_digit x t b) (nth_digit y t b) (Suc c) = 0"
        using sum_carry_formula[where ?k = "c"] bin_carry_bounded[where ?k = "c"]
        using assms(5-6) by (metis Suc_eq_plus1 add_cancel_left_left mod_div_trivial)

      (* inductive step *)
      {
        fix n
        assume n: "n \<ge> Suc c"
        assume IH: "bin_carry (nth_digit x t b) (nth_digit y t b) n = 0"
        have "bin_carry (nth_digit x t b) (nth_digit y t b) (Suc n)
          = (nth_digit x t b \<exclamdown> n + nth_digit y t b \<exclamdown> n
          + bin_carry (nth_digit x t b) (nth_digit y t b) n) div 2" 
          using sum_carry_formula[of "nth_digit x t b" "nth_digit y t b"] by auto
        also have "... = bin_carry (nth_digit x t b) (nth_digit y t b) n div 2"
          using x_digit_bound y_digit_bound n by auto
        also have "... = 0" using IH by auto

        finally have "bin_carry (nth_digit x t b) (nth_digit y t b) (Suc n) = 0"
          by auto
      }
  
      then show ?thesis
        using k base
        using nat_induct_at_least[where ?P = "\<lambda>k. bin_carry (nth_digit x t b) 
                                                            (nth_digit y t b) k = 0"]
        by auto
    qed

    have "(nth_digit x t b + nth_digit y t b) \<exclamdown> k 
        = (nth_digit x t b \<exclamdown> k + nth_digit y t b \<exclamdown> k 
        + bin_carry (nth_digit x t b) (nth_digit y t b) k) mod 2"
      using sum_digit_formula[of "nth_digit x t b" "nth_digit y t b" "k"] by auto
    hence separate_sum: "(nth_digit x t b + nth_digit y t b) \<exclamdown> k = 0" 
      using x_digit_bound y_digit_bound carry0 k by auto
    
    have "nth_digit (x+y) t b < b" 
      using nth_digit_bound b_def by auto
    hence xy_sum: "nth_digit (x+y) t b \<exclamdown> k = 0"
      using nth_bit_def b_def aux_lt_implies_mask b_def k by metis
    from xy_sum separate_sum have k_ge: "nth_digit (x+y) t b \<exclamdown> k
                                  = (nth_digit x t b + nth_digit y t b) \<exclamdown> k"
      by auto
  }
  hence k_ge: "k\<ge>Suc c \<longrightarrow> nth_digit (x+y) t b \<exclamdown> k
                         = (nth_digit x t b + nth_digit y t b) \<exclamdown> k" for k
    by auto

  moreover have k_lt:"k<Suc c \<longrightarrow> nth_digit (x+y) t b \<exclamdown> k 
                               = (nth_digit x t b + nth_digit y t b) \<exclamdown> k" for k
    using digit_wise_block_additivity assms by auto

  ultimately have "nth_digit (x+y) t b \<exclamdown> k 
                = (nth_digit x t b + nth_digit y t b) \<exclamdown> k" for k
    by(cases "k<Suc c"; auto)

  thus ?thesis using digit_wise_equiv[of "nth_digit (x+y) t b"] by auto
qed

lemma block_to_sum:
  assumes "c>0"
  defines b: "b \<equiv> 2 ^ (Suc c)"
  assumes yltx_digits: "\<forall>t'. nth_digit y t' b \<le> nth_digit x t' b"
  shows "y mod b^t \<le> x mod b^t"
proof(cases "t=0")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis using yltx_digits apply(induct t, auto) using yltx_digits
    by (smt add.commute add_left_cancel add_mono_thms_linordered_semiring(1) mod_mult2_eq 
        mult_le_cancel2 nth_digit_def semiring_normalization_rules(7))
qed

lemma narry_gen_pow2_reduct:
  assumes "c>0"
  defines b: "b \<equiv> 2 ^ (Suc c)"
  assumes yltx_digits: "\<forall>t'. nth_digit y t' b \<le> nth_digit x t' b"
  shows "k\<le>c \<Longrightarrow> bin_narry (nth_digit x t b) (nth_digit y t b) k
    = bin_narry x y (Suc c * t + k)"
proof (induction k)
  case 0
  then show ?case
  proof (cases "t=0")
    case True
    then show ?thesis by (simp add: bin_narry_def)
  next
    case False
    have "bin_narry x y (Suc c * t) = 0" using yltx_digits block_to_sum bin_narry_def assms
      by (metis not_less power_mult)
    then show ?thesis by (simp add: bin_narry_def)
  qed
next
  case (Suc k)
  have ylex: "y\<le>x" using yltx_digits digitwise_leq b Suc_1 lessI power_gt1 by metis
  have "k<Suc c \<Longrightarrow> x \<exclamdown> (Suc c * t + k) = nth_digit x t b \<exclamdown> k" 
    using digit_gen_pow2_reduct[of "k" "Suc c" "x" "t"] b by auto
  moreover have "k<Suc c \<Longrightarrow> y \<exclamdown> (Suc c * t + k) = nth_digit y t b \<exclamdown> k"
    using digit_gen_pow2_reduct[of "k" "Suc c" "y" "t"] b by auto
  ultimately show ?case using Suc yltx_digits 
      dif_narry_formula[of "(nth_digit y t b)" "(nth_digit x t b)" k] 
      dif_narry_formula[of y x "Suc c * t + k"] ylex by auto
qed
  
lemma digit_wise_block_subtractivity:
  fixes c
  defines "b \<equiv> 2 ^ Suc c" 
  assumes yltx_digits: "\<forall>t'. nth_digit y t' b \<le> nth_digit x t' b"
      and "k\<le>c"
      and "c>0"
  shows "nth_digit (x-y) t b \<exclamdown> k = (nth_digit x t b - nth_digit y t b) \<exclamdown> k"
proof -
  have x: "nth_digit x t b \<exclamdown> k = x \<exclamdown> (Suc c * t + k)"
    using digit_gen_pow2_reduct[of "k" "Suc c" "x" "t"] b_def `k\<le>c` by auto
  have y: "nth_digit y t b \<exclamdown> k = y \<exclamdown> (Suc c * t + k)" 
    using digit_gen_pow2_reduct[of "k" "Suc c" "y" "t"] b_def `k\<le>c` by auto

  have "b > 1" using `c>0` b_def
    by (metis Suc_1 lessI power_gt1)
  then have yltx: "y \<le> x" using digitwise_leq yltx_digits by auto

  have "(nth_digit x t b - nth_digit y t b) \<exclamdown> k 
      = ((nth_digit x t b) \<exclamdown> k + (nth_digit y t b) \<exclamdown> k
        + bin_narry (nth_digit x t b) (nth_digit y t b) k) mod 2"
    using dif_digit_formula yltx_digits by auto
  also have "... = (x \<exclamdown> (Suc c * t + k) + y \<exclamdown> (Suc c * t + k)
                    + bin_narry (nth_digit x t b) (nth_digit y t b) k) mod 2"
    using x y by auto 
  also have "... = (x \<exclamdown> (Suc c * t + k) + y \<exclamdown> (Suc c * t + k)
                    + bin_narry x y (Suc c * t + k)) mod 2"
  using narry_gen_pow2_reduct using assms(3) assms(4) b_def yltx_digits by auto
  also have "... = nth_digit (x-y) t b \<exclamdown> k"
    using digit_gen_pow2_reduct[of "k" "Suc c" "x-y" "t"] b_def `k\<le>c` dif_digit_formula yltx 
    by auto
  finally show ?thesis by auto
qed

lemma block_subtractivity:
  assumes "c > 0"
  defines "b \<equiv> 2 ^ Suc c"
  assumes block_wise_lt: "\<forall>t'. nth_digit y t' b \<le> nth_digit x t' b"
  shows "nth_digit (x-y) t b = nth_digit x t b - nth_digit y t b" 
proof -
  have "k\<le>c \<longrightarrow> nth_digit (x-y) t b \<exclamdown> k = (x - y) \<exclamdown> (Suc c * t + k)" for k 
    using digit_gen_pow2_reduct[of "k" "Suc c" "x-y" "t"] b_def by auto
  have "k\<le>c \<longrightarrow> nth_digit x t b \<exclamdown> k = x \<exclamdown> (Suc c * t + k)" for k 
    using digit_gen_pow2_reduct[of "k" "Suc c" "x" "t"] b_def by auto
  have "k\<le>c \<longrightarrow> nth_digit y t b \<exclamdown> k = y \<exclamdown> (Suc c * t + k)" for k 
    using digit_gen_pow2_reduct[of "k" "Suc c" "y" "t"] b_def by auto

  have k_le: "k \<le> c \<longrightarrow> nth_digit (x-y) t b \<exclamdown> k
               = (nth_digit x t b - nth_digit y t b) \<exclamdown> k" for k 
    using assms digit_wise_block_subtractivity by auto

  have "nth_digit x t b - nth_digit y t b < b" using 
      nth_digit_bound b_def by (simp add: less_imp_diff_less) 
  hence diff: "k\<ge>Suc c \<longrightarrow> (nth_digit x t b - nth_digit y t b) \<exclamdown> k = 0" for k
    using nth_bit_def b_def aux_lt_implies_mask b_def by metis
  
  have "nth_digit (x-y) t b < b" using nth_digit_bound b_def by auto
  hence "k\<ge>Suc c \<longrightarrow> nth_digit (x-y) t b \<exclamdown> k = 0" for k 
    using nth_bit_def b_def aux_lt_implies_mask b_def by metis
  with diff have k_gt: "k > c \<longrightarrow> nth_digit (x-y) t b \<exclamdown> k
               = (nth_digit x t b - nth_digit y t b) \<exclamdown> k" for k 
    by auto
  from k_le k_gt have "nth_digit (x-y) t b \<exclamdown> k 
              = (nth_digit x t b - nth_digit y t b) \<exclamdown> k" for k by(cases "k>c"; auto)
  thus ?thesis using digit_wise_equiv[of "nth_digit x t b - nth_digit y t b" 
                                         "nth_digit (x-y) t b"] by auto
qed

lemma bitAND_nth_digit_commute:
  assumes b_def: "b = 2^(Suc c)"
  shows "nth_digit (x && y) t b = nth_digit x t b && nth_digit y t b"
proof -
  {
    fix k
    assume k: "k < Suc c"
    have prod: "nth_digit (x && y) t b \<exclamdown> k = (x && y) \<exclamdown> (Suc c * t + k)"
      using digit_gen_pow2_reduct[of _ "Suc c" "x && y" "t"] b_def k by auto
    moreover have x: "nth_digit x t b \<exclamdown> k = x \<exclamdown> (Suc c * t + k)"
      using digit_gen_pow2_reduct[of _ "Suc c" "x"] b_def k by auto
    moreover have y: "nth_digit y t b \<exclamdown> k = y \<exclamdown> (Suc c * t + k)"
      using digit_gen_pow2_reduct[of _ "Suc c" "y"] b_def k by auto
    moreover have "(x && y) \<exclamdown> (Suc c * t + k) = (x \<exclamdown> (Suc c * t + k)) * (y \<exclamdown> (Suc c * t + k))"
      using bitAND_digit_mult by auto
  
    ultimately have "nth_digit (x && y) t b \<exclamdown> k
                     = nth_digit x t b \<exclamdown> k * nth_digit y t b \<exclamdown> k"
      by auto
  
    also have "... = (nth_digit x t b && nth_digit y t b) \<exclamdown> k"
      using bitAND_digit_mult by auto

    finally have "nth_digit (x && y) t b \<exclamdown> k
                  = (nth_digit x t b && nth_digit y t b) \<exclamdown> k"
      by auto
  }

  (* now also consider k \<ge> Suc c *)
  then have "nth_digit (x && y) t b \<exclamdown> k
                  = (nth_digit x t b && nth_digit y t b) \<exclamdown> k" for k
    by (metis aux_lt_implies_mask b_def bitAND_digit_mult leI mult_eq_0_iff nth_digit_bound)

  then show ?thesis using b_def digit_wise_equiv[of "nth_digit (x && y) t b"] by auto
qed

lemma bx_aux:
  shows "b>1 \<Longrightarrow> nth_digit (b^x) t' b = (if x=t' then 1 else 0)"
  by (cases "t' > x", auto simp: nth_digit_def)
     (metis dvd_imp_mod_0 dvd_power leI less_SucI nat_neq_iff power_diff zero_less_diff)


context
  fixes c b :: nat
  assumes b_def: "b \<equiv> 2^(Suc c)"
  assumes c_gt0: "c>0"
begin

lemma b_gt1: "b>1" using c_gt0 b_def
  using one_less_numeral_iff one_less_power semiring_norm(76) by blast

text \<open>Commutation relations with sums\<close>

(* Commute outside, need assumption for nth_digit inside sum *)

lemma finite_sum_nth_digit_commute:
  fixes M :: nat
  shows "\<forall>t. \<forall>k\<le>M. nth_digit (fct k) t b < 2^c \<Longrightarrow>
         \<forall>t. (\<Sum>i=0..M. nth_digit (fct i) t b) < 2^c \<Longrightarrow>
         nth_digit (\<Sum>i=0..M. fct i) t b = (\<Sum>i=0..M. (nth_digit (fct i) t b))"
proof (induct M arbitrary: t)
  case 0 thus ?case by auto
next
  case (Suc M)

  have assm1: "\<forall>t. \<forall>k\<le>Suc M. nth_digit (fct k) t b < 2^c"
    using Suc.prems by auto
  have assm1_reduced: "\<forall>t. \<forall>k\<le>M. nth_digit (fct k) t b < 2^c"
    using assm1 by auto
  have nocarry2: "\<forall>t. \<forall>k\<le>Suc M. nth_digit (fct k) t b \<exclamdown> c = 0"
    using assm1 nth_bit_def by auto

  have assm2:
    "\<forall>t. nth_digit (fct (Suc M)) t b + (\<Sum>i=0..M. nth_digit (fct i) t b) < 2^c"
    using Suc.prems by (simp add: add.commute)
  hence assm2_reduced: "\<forall>t. (\<Sum>i=0..M. nth_digit (fct i) t b) < 2^c"
    using Suc.prems(2) add_lessD1 by fastforce

  have IH: "\<forall>t. nth_digit (\<Sum>i=0..M. fct i) t b
                = (\<Sum>i=0..M. nth_digit (fct i) t b)"
    using assm1_reduced assm2_reduced Suc.hyps by blast
  then have assm2_IH_commuted: "\<forall>t. nth_digit (\<Sum>i=0..M. fct i) t b < 2^c"
    using assm2_reduced by auto
  hence nocarry3: "\<forall>t. nth_digit (\<Sum>i=0..M. fct i) t b \<exclamdown> c = 0"
    using aux_lt_implies_mask by blast

  have 1: "nth_digit (sum fct {0..M}) (t - 1) b \<exclamdown> c = 0" using nocarry3 by auto
  have 2: "nth_digit (fct (Suc M)) (t - 1) b \<exclamdown> c = 0" using nocarry2 by auto
  have 3: "nth_digit (sum fct {0..M}) t b \<exclamdown> c = 0" using nocarry3 by auto 
  have 4: "nth_digit (fct (Suc M)) t b \<exclamdown> c = 0" using nocarry2 by auto
  from block_additivity show ?case using 1 2 3 4 c_gt0 Suc b_def
    using IH by auto
qed

lemma sum_nth_digit_commute_aux:
  fixes g
  defines SX_def: "SX \<equiv> \<lambda>l m (fct :: nat \<Rightarrow> nat). (\<Sum>k = 0..m. if g l k then fct k else 0)"
    assumes nocarry: "\<forall>t. \<forall>k\<le>M. nth_digit (fct k) t b < 2^c"
    and nocarry_sum: "\<forall>t. (SX l M (\<lambda>k. nth_digit (fct k) t b)) < 2^c"
  shows "nth_digit (SX l M fct) t b = SX l M (\<lambda>k. nth_digit (fct k) t b)"
proof -
  have aux: "nth_digit (if g l i then fct i else 0) t b
              = (if g l i then nth_digit (fct i) t b else 0)" for i t
    using aux1_digit_wise_gen_equiv b_gt1 by auto

  from nocarry have "\<forall>t. \<forall>k\<le>M. nth_digit (if g l k then fct k else 0) t b < 2^c"
    using aux by auto

  moreover from nocarry_sum have
    "\<forall>t. (\<Sum>i = 0..M. nth_digit (if g l i then fct i else 0) t b) < 2 ^ c"
    unfolding SX_def by (auto simp: aux)

  ultimately have "nth_digit (\<Sum>k = 0..M. if g l k then fct k else 0) t b
      = (\<Sum>k = 0..M. nth_digit (if g l k then fct k else 0) t b)" 
    using finite_sum_nth_digit_commute[where ?fct = "\<lambda>k. if g l k then fct k else 0"]
    by (simp add: SX_def)
  moreover have "\<forall>k. nth_digit (if g l k then fct k else 0) t b
                 = (if g l k then nth_digit (fct k) t b else 0)"
    by (auto simp: nth_digit_def)
  ultimately show ?thesis by (auto simp: SX_def)
qed

lemma sum_nth_digit_commute:
  fixes g
  defines SX_def: "SX \<equiv> \<lambda>p l (fct :: nat \<Rightarrow> nat). (\<Sum>k = 0..length p - 1. if g l k then fct k else 0)"
    assumes nocarry: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (fct k) t b < 2^c"
    and nocarry_sum: "\<forall>t. (SX p l (\<lambda>k. nth_digit (fct k) t b)) < 2^c"
  shows "nth_digit (SX p l fct) t b = SX p l (\<lambda>k. nth_digit (fct k) t b)"
proof -
  let ?m = "length p - 1"

  have "\<forall>t. (\<Sum>k = 0..?m. if g l k then nth_digit (fct k) t b else 0) < 2^c"
    using nocarry_sum unfolding SX_def by blast

  then have "nth_digit (\<Sum>k = 0..length p - 1. if g l k then fct k else 0) t b
             = (\<Sum>k = 0..length p - 1. if g l k then nth_digit (fct k) t b else 0)"
    using nocarry
    using sum_nth_digit_commute_aux[where ?M = "length p - 1"]
    by auto

  then show ?thesis using SX_def by auto
qed

text \<open>Commute inside, need assumption for all partial sums\<close>
lemma finite_sum_nth_digit_commute2: 
  fixes M :: nat
  shows "\<forall>t. \<forall>k\<le>M. nth_digit (fct k) t b < 2^c \<Longrightarrow>
         \<forall>t. \<forall>m\<le>M. nth_digit (\<Sum>i=0..m. fct i) t b < 2^c \<Longrightarrow>
         nth_digit (\<Sum>i=0..M. fct i) t b = (\<Sum>i=0..M. (nth_digit (fct i) t b))"
proof (induct M arbitrary: t)
  case 0 thus ?case by auto
next
  case (Suc M)

  have assm1: "\<forall>t. \<forall>k\<le>Suc M. nth_digit (fct k) t b < 2^c"
    using Suc.prems by auto
  have assm1_reduced: "\<forall>t. \<forall>k\<le>M. nth_digit (fct k) t b < 2^c"
    using assm1 by auto
  have nocarry2: "\<forall>t. \<forall>k\<le>Suc M. nth_digit (fct k) t b \<exclamdown> c = 0"
    using assm1 nth_bit_def by auto

  have assm2:
    "\<forall>t. nth_digit (\<Sum>i=0..M. (fct i)) t b < 2^c"
    using Suc.prems by (simp add: add.commute)
  hence nocarry3: "\<forall>t. nth_digit (\<Sum>i=0..M. fct i) t b \<exclamdown> c = 0"
    using aux_lt_implies_mask by blast

  have 1: "nth_digit (sum fct {0..M}) (t - 1) b \<exclamdown> c = 0" using nocarry3 by auto
  have 2: "nth_digit (fct (Suc M)) (t - 1) b \<exclamdown> c = 0" using nocarry2 by auto
  have 3: "nth_digit (sum fct {0..M}) t b \<exclamdown> c = 0" using nocarry3 by auto 
  have 4: "nth_digit (fct (Suc M)) t b \<exclamdown> c = 0" using nocarry2 by auto
  from block_additivity show ?case using 1 2 3 4 c_gt0 Suc b_def by auto
qed

lemma sum_nth_digit_commute_aux2:
  fixes g
  defines SX_def: "SX \<equiv> \<lambda>l m (fct :: nat \<Rightarrow> nat). (\<Sum>k = 0..m. if g l k then fct k else 0)"
    assumes nocarry: "\<forall>t. \<forall>k\<le>M. nth_digit (fct k) t b < 2^c"
    and nocarry_sum: "\<forall>t. \<forall>m\<le>M. nth_digit (SX l m fct) t b < 2^c"
  shows "nth_digit (SX l M fct) t b = SX l M (\<lambda>k. nth_digit (fct k) t b)"
proof -
  have aux: "nth_digit (if g l i then fct i else 0) t b
              = (if g l i then nth_digit (fct i) t b else 0)" for i t
    using aux1_digit_wise_gen_equiv b_gt1 by auto

  from nocarry have "\<forall>t. \<forall>k\<le>M. nth_digit (if g l k then fct k else 0) t b < 2^c"
    using aux by auto

  moreover from nocarry_sum have
    "\<forall>t. \<forall>m\<le>M. nth_digit (\<Sum>i = 0..m. (if g l i then fct i else 0)) t b < 2 ^ c"
    unfolding SX_def by (auto simp: aux)

  ultimately have "nth_digit (\<Sum>k = 0..M. if g l k then fct k else 0) t b
      = (\<Sum>k = 0..M. nth_digit (if g l k then fct k else 0) t b)" 
    using finite_sum_nth_digit_commute2[where ?fct = "\<lambda>k. if g l k then fct k else 0"]
    by (simp add: SX_def)
  moreover have "\<forall>k. nth_digit (if g l k then fct k else 0) t b
                 = (if g l k then nth_digit (fct k) t b else 0)"
    by (auto simp: nth_digit_def)
  ultimately show ?thesis by (auto simp: SX_def)
qed

lemma sum_nth_digit_commute2:
  fixes g p
  defines SX_def: "SX \<equiv> \<lambda>p l (fct :: nat \<Rightarrow> nat). (\<Sum>k = 0..length p - 1. if g l k then fct k else 0)"
    assumes nocarry: "\<forall>t. \<forall>k\<le>length p - 1. nth_digit (fct k) t b < 2^c"
    and nocarry_sum: "\<forall>t. \<forall>m\<le>length p - 1. nth_digit (SX (take (Suc m) p) l fct) t b < 2^c"
  shows "nth_digit (SX p l fct) t b = SX p l (\<lambda>k. nth_digit (fct k) t b)"
proof -
  have "\<forall>m \<le> length p - 1. (SX (take (Suc m) p) l fct) = (\<Sum>k = 0..m. if g l k then fct k else 0)"
    unfolding SX_def
    by (auto) (metis (no_types, lifting) One_nat_def diff_Suc_1 min_absorb2 min_diff)
  hence "\<forall>t m. m \<le> length p - 1 \<longrightarrow> 
            nth_digit (\<Sum>k = 0..m.  if g l k then fct k else 0) t b < 2 ^ c"
    using nocarry_sum by auto

  then have "nth_digit (\<Sum>k = 0..length p - 1. if g l k then fct k else 0) t b
             = (\<Sum>k = 0..length p - 1. if g l k then nth_digit (fct k) t b else 0)"
    using nocarry
    using sum_nth_digit_commute_aux2[where ?M = "length p - 1" and ?fct = "fct" and ?g = g]
    by blast

  then show ?thesis using SX_def by auto
qed

end 

end