subsection \<open>Masking properties\<close>

theory MachineMasking
  imports RegisterMachineSimulation "../Diophantine/Binary_And"
begin

(* [D] 4.18 *)
definition E :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "(E q b) = (\<Sum>t = 0..q. b^t)"

lemma e_geom_series:
  assumes "b \<ge> 2"
  shows "(E q b = e) \<longleftrightarrow> ((b-1) * e = b^(Suc q) - 1 )" (is "?P \<longleftrightarrow> ?Q")
proof-
  have "sum ((^) (int b)) {..<Suc q} = sum ((^) b) {0..q}" by (simp add: atLeast0AtMost lessThan_Suc_atMost)
  then have "(int b - 1) *  (E q b) = int b ^ Suc q - 1"
    using E_def by (metis power_diff_1_eq)
  moreover have "int b ^ Suc q - 1 =  b ^ (Suc q) - 1" using one_le_power[of "int b" "Suc q"] assms 
    by (simp add: of_nat_diff)
  moreover have "int b - 1 = b - 1 " using assms by auto
  ultimately show ?thesis using assms
    by (metis Suc_1 Suc_diff_le Zero_not_Suc diff_Suc_Suc int_ops(7) mult_cancel_left of_nat_eq_iff)
qed


(* [D] 4.16 *)
definition D :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "(D q c b) = (\<Sum>t = 0..q. (2^c - 1) * b^t)"

lemma d_geom_series:
  assumes "b = 2^(Suc c)"
  shows "(D q c b = d) \<longleftrightarrow> ((b-1) * d = (2^c - 1) * (b^(Suc q) - 1))" (is "?P \<longleftrightarrow> ?Q")
proof-
  have "D q c b = (2^c - 1) *  E q b" by (auto simp: E_def D_def sum_distrib_left sum_distrib_right)
  moreover have "b \<ge> 2" using assms by fastforce
  ultimately show ?thesis by (smt e_geom_series mult.left_commute mult_cancel_left)
qed

(* [D] 4.21 *)
definition F :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "(F q c b) = (\<Sum>t = 0..q. 2^c * b^t)"

lemma f_geom_series:
  assumes "b = 2^(Suc c)"
  shows "(F q c b = f) \<longleftrightarrow> ( (b-1) * f = 2^c * (b^(Suc q) - 1) )"
proof-
  have "F q c b = 2^c *  E q b" by (auto simp: E_def F_def sum_distrib_left sum_distrib_right)
  moreover have "b \<ge> 2" using assms by fastforce
  ultimately show ?thesis by (smt e_geom_series mult.left_commute mult_cancel_left)
qed

(* AUX LEMMAS *)
lemma aux_lt_implies_mask:
  assumes "a < 2^k"
  shows "\<forall>r\<ge>k. a \<exclamdown> r = 0"
  using nth_bit_def assms apply auto
proof - (* found by e *)
  fix r :: nat
  assume a1: "a < 2 ^ k"
  assume a2: "k \<le> r"
  from a1 have "a div 2 ^ k = 0"
    by simp
  then have "2 = (0::nat) \<or> a < 2 ^ r"
    using a2 by (metis (no_types) div_le_mono nat_zero_less_power_iff neq0_conv not_le power_diff)
  then show "a div 2 ^ r mod 2 = 0"
    by simp
qed

lemma lt_implies_mask:
  fixes a b :: nat
  assumes "\<exists>k. a < 2^k \<and> (\<forall>r<k. nth_bit b r = 1)" (* this means a < b and b = xx11..11 *)
  shows "a \<preceq> b"
proof -
  obtain k where assms: "a < 2^k \<and> (\<forall>r<k. nth_bit b r = 1)" using assms by auto
  have k1: "\<forall>r<k. a \<exclamdown> r \<le> b \<exclamdown> r" using nth_bit_bounded
    by (simp add: \<open>a < 2 ^ k \<and> (\<forall>r<k. b \<exclamdown> r = 1)\<close>)
  hence k2: "\<forall>r\<ge>k. a \<exclamdown> r = 0" using aux_lt_implies_mask assms by auto
  show ?thesis using masks_leq_equiv
    by auto (metis k1 k2 le0 not_less)
qed

lemma mask_conversed_shift:
  fixes a b k :: nat
  assumes asm: "a \<preceq> b"
  shows "a * 2^k \<preceq> b * 2^k"
proof -
  have shift: "x \<preceq> y \<Longrightarrow> 2*x \<preceq> 2*y" for x y by (induction x; auto)
  have "a * 2 ^ k \<preceq> b * 2 ^ k \<Longrightarrow> 2 * (a * 2 ^ k) \<preceq> 2 * (b * 2 ^ k)" for k
    using shift[of "a*2^k" "b*2^k"] by auto
  thus ?thesis by (induction k; auto simp: asm shift algebra_simps)
qed

lemma base_summation_bound:
  fixes c q :: nat
    and f :: "(nat \<Rightarrow> nat)"

defines b: "b \<equiv> B c"
assumes bound: "\<forall>t. f t < 2 ^ Suc c - (1::nat)"

shows "(\<Sum>t = 0..q. f t * b^t) < b^(Suc q)"
proof (induction q)
  case 0
  then show ?case using B_def b bound less_imp_diff_less not_less_eq
    by auto blast
next
  case (Suc q)
  have "(\<Sum>t = 0..Suc q. f t * b ^ t) = f (Suc q) * b ^ (Suc q) + (\<Sum>t = 0..q. f t * b ^ t)"
    by (auto cong: sum.cong)
  also have "... < (f (Suc q) + 1) * b ^ (Suc q)"
    using Suc.IH by auto
  also have "... < b * b ^ (Suc q)"
    by (metis bound b less_diff_conv B_def mult_less_cancel2 zero_less_numeral zero_less_power)
  finally show ?case by auto
qed

lemma mask_conserved_sum:
  fixes y c q :: nat
    and x :: "(nat \<Rightarrow> nat)"

defines b: "b \<equiv> B c"
assumes mask: "\<forall>t. x t \<preceq> y"
assumes xlt: "\<forall>t. x t \<le> 2 ^ c - Suc 0"
assumes ylt: "y \<le> 2 ^ c - Suc 0"

shows "(\<Sum>t = 0..q. x t * b^t) \<preceq> (\<Sum>t = 0..q. y * b^t)"
proof (induction q)
  case 0
  then show ?case
    using mask by auto
next
  case (Suc q)

  have xb: "\<forall>t. x t < 2^Suc c - Suc 0"
    using xlt
    by (smt Suc_pred leI le_imp_less_Suc less_SucE less_trans n_less_m_mult_n numeral_2_eq_2 
        power.simps(2) zero_less_numeral zero_less_power)
  have yb: "y < 2^c"
    using ylt b B_def leI order_trans by fastforce

  have sumxlt: "(\<Sum>t = 0..q. x t * b ^ t) < b^(Suc q)"
    using base_summation_bound xb b B_def by auto
  have sumylt: "(\<Sum>t = 0..q. y * b ^ t) < b^(Suc q)"
    using base_summation_bound yb b B_def by auto

  have "((\<Sum>t = 0..Suc q. x t * b ^ t) \<preceq> (\<Sum>t = 0..Suc q. y * b ^ t))
      = (x (Suc q) * b^Suc q + (\<Sum>t = 0..q. x t * b ^ t) \<preceq>
                 y * b^Suc q + (\<Sum>t = 0..q. y * b ^ t))"
    by (auto simp: atLeast0_lessThan_Suc add.commute)
  also have "... = (x (Suc q) * b^Suc q \<preceq> y * b^Suc q)
                 \<and> (\<Sum>t = 0..q. x t * b ^ t) \<preceq> (\<Sum>t = 0..q. y * b ^ t)"
    using mask_linear[where ?t = "Suc c * Suc q"] sumxlt sumylt Suc.IH b B_def
    apply auto
    apply (smt mask mask_conversed_shift power_Suc power_mult power_mult_distrib)
    by (smt mask mask_linear power_Suc power_mult power_mult_distrib)
  finally show ?case using mask_linear Suc.IH B_def
    by (metis (no_types, lifting) b mask mask_conversed_shift power_mult)
qed

lemma aux_powertwo_digits:
  fixes k c :: nat
  assumes "k < c"
  shows "nth_bit (2^c) k = 0"
proof -
  have h: "(2::nat) ^ c div 2 ^ k = 2 ^ (c - k)"
    by (simp add: assms less_imp_le power_diff)
  thus ?thesis
    by (auto simp: h nth_bit_def assms)
qed

lemma obtain_digit_rep:
  fixes x c :: nat
  shows "x && 2^c = (\<Sum>t<Suc c. 2^t * (nth_bit x t) * (nth_bit (2^c) t))"
proof -
  have "x && 2^c \<preceq> 2^c" by (simp add: lm0245)
  hence "x && 2^c \<le> 2^c" by (simp add: masks_leq)
  hence h: "x && 2^c < 2^Suc c"
    by (smt Suc_lessD le_neq_implies_less lessI less_trans_Suc n_less_m_mult_n numeral_2_eq_2 
        power_Suc zero_less_power)
  have "\<forall>t. (x && 2^c) \<exclamdown> t = (nth_bit x t) * (nth_bit (2^c) t)"
    using bitAND_digit_mult by auto
  then show ?thesis using h digit_sum_repr[of "(x && 2^c)" "Suc c"]
    by (auto) (simp add: mult.commute semiring_normalization_rules(19))
qed

lemma nth_digit_bitAND_equiv:
  fixes x c :: nat
  shows "2^c * nth_bit x c = (x && 2^c)"
proof -
  have d1: "nth_bit (2^c) c = 1"
    using nth_bit_def by auto

  moreover have "x && 2^c = (2::nat)^c * (x \<exclamdown> c) * (((2::nat)^c) \<exclamdown> c)
            + (\<Sum>t<c. (2::nat)^t * (x \<exclamdown> t) * (((2::nat)^c) \<exclamdown> t))"
    using obtain_digit_rep by (auto cong: sum.cong)

  moreover have "(\<Sum>t<c. 2^t * (nth_bit x t) * (nth_bit ((2::nat)^c) t)) = 0"
    using aux_powertwo_digits by auto

  ultimately show ?thesis using d1
    by auto
qed

lemma bitAND_single_digit:
  fixes x c :: nat
assumes "2 ^ c \<le> x"
assumes "x < 2 ^ Suc c"

shows "nth_bit x c = 1"
proof -
  obtain b where b: "x = 2^c + b"
    using assms(1) le_Suc_ex by auto
  have bb: "b < 2^c"
    using assms(2) b by auto
  have "(2 ^ c + b) div 2 ^ c mod 2 = (1 + b div 2 ^ c) mod 2"
    by (auto simp: div_add_self1)
  also have "... = 1"
    by (auto simp: bb)
  finally show ?thesis
    by (simp only: nth_bit_def b)
qed

lemma aux_bitAND_distrib: "2 * (a && b) = (2 * a) && (2 * b)"
  by (induct a b rule: bitAND_nat.induct; auto)

lemma bitAND_distrib: "2^c * (a && b) = (2^c * a) && (2^c * b)"
proof (induction c)
  case 0
  then show ?case by auto
next
  case (Suc c)
  have "2 ^ Suc c * (a && b) = 2 * (2 ^ c * (a && b))" by auto
  also have "... = 2 * ((2^c * a) && (2^c * b))" using Suc.IH by auto
  also have "... = ((2^Suc c * a) && (2^Suc c * b))"
    using aux_bitAND_distrib[of "2^c * a" "2^c * b"]
    by (auto simp add: ab_semigroup_mult_class.mult_ac(1))
  finally show ?case by auto
qed

lemma bitAND_linear_sum:
  fixes x y :: "nat \<Rightarrow> nat"
    and c :: nat
    and q :: nat

defines b: "b == 2 ^ Suc c"

assumes xb: "\<forall>t. x t < 2 ^ Suc c - 1"
assumes yb: "\<forall>t. y t < 2 ^ Suc c - 1"

shows "(\<Sum>t = 0..q. (x t && y t) * b^t) =
       (\<Sum>t = 0..q. x t * b^t) && (\<Sum>t = 0..q. y t * b^t)"
proof (induction q)
  case 0
  then show ?case
    by (auto simp: b B_def)
next
  case (Suc q)
  have "(\<Sum>t = 0..Suc q. (x t && y t) * b ^ t) = (x (Suc q) && y (Suc q)) * b ^ Suc q
                                               + (\<Sum>t = 0..q. (x t && y t) * b ^ t)"
    by (auto cong: sum.cong)

  moreover have h0: "(x (Suc q) && y (Suc q)) * b ^ Suc q 
                   = (x (Suc q) * b^Suc q) && (y (Suc q) * b^Suc q)"
    using b bitAND_distrib by (auto) (smt mult.commute power_Suc power_mult)

  moreover have h1: "(\<Sum>t = 0..q. (x t && y t) * b ^ t) 
                   = (\<Sum>t = 0..q. x t * b^t) && (\<Sum>t = 0..q. y t * b^t)"
    using Suc.IH by auto

  ultimately have h2: "(\<Sum>t = 0..Suc q. (x t && y t) * b ^ t)
                = ((x (Suc q) * b^Suc q) && (y (Suc q) * b^Suc q))
                + ((\<Sum>t = 0..q. x t * b^t) && (\<Sum>t = 0..q. y t * b^t))"
    by auto

  have sumxb: "(\<Sum>t = 0..q. x t * b ^ t) < b ^ Suc q"
    using base_summation_bound xb b B_def by auto
  have sumyb: "(\<Sum>t = 0..q. y t * b ^ t) < b ^ Suc q"
    using base_summation_bound yb b B_def by auto

  have h3: "((x (Suc q) * b^Suc q) && (y (Suc q) * b^Suc q)) 
          + ((\<Sum>t = 0..q. x t * b^t) && (\<Sum>t = 0..q. y t * b^t))
          = ((\<Sum>t = 0..q. x t * b^t) + x (Suc q) * b^Suc q) 
         && ((\<Sum>t = 0..q. y t * b^t) + y (Suc q) * b^Suc q)"
    using sumxb sumyb bitAND_linear h2 h0
    by (auto) (smt add.commute b power_Suc power_mult)

  thus ?case using h2 by (auto cong: sum.cong)
qed

lemma dmask_aux0:
  fixes x :: nat
  assumes "x > 0"
  shows "(2 ^ x - Suc 0) div 2 = 2 ^ (x - 1) - Suc 0"
proof -
  have 0: "(2^x - Suc 0) div 2 = (2^x - 2) div 2"
    by (smt Suc_diff_Suc Suc_pred assms dvd_power even_Suc even_Suc_div_two nat_power_eq_Suc_0_iff
            neq0_conv numeral_2_eq_2 zero_less_diff zero_less_power)
    (* can do manual parity distinction *)
  moreover have divides: "(2::nat) dvd 2^x"
    by (simp add: assms dvd_power[of x "2::nat"]) 
  moreover have "(2^x - 2::nat) div 2 = 2^x div 2 - 2 div 2"
    using div_plus_div_distrib_dvd_left[of "2" "2^x" "2"] divides
    by auto
  moreover have "... = 2 ^ (x - 1) - Suc 0"
    by (simp add: Suc_leI assms power_diff)
  ultimately have 1: "(2 ^ x - Suc 0) div 2 = 2 ^ (x - 1) - Suc 0"
     by (smt One_nat_def)
  thus ?thesis by simp
qed

lemma dmask_aux:
  fixes c :: nat
  shows "d < c \<Longrightarrow> (2^c - Suc 0) div 2^d = 2 ^ (c - d) - Suc 0"
proof (induction d)
  case 0
  then show ?case by (auto)
next
  case (Suc d)
  have d: "d < c" using Suc.prems by auto
  have "(2 ^ c - Suc 0) div 2 ^ Suc d = (2 ^ c - Suc 0) div 2 ^ d div 2"
    by (auto) (metis mult.commute div_mult2_eq)
  also have "... = (2 ^ (c - d) - Suc 0) div 2"
    by (subst Suc.IH) (auto simp: d)
  also have "... = 2 ^ (c - Suc d) - Suc 0"
    apply (subst dmask_aux0[of "c - d"])
    using d by (auto)
  finally show ?case by auto
qed


(* REGISTERS *)
lemma register_cells_masked:
  fixes l :: register
    and t :: nat
    and ic :: configuration
    and p :: program

assumes cells_bounded: "cells_bounded ic p c"
assumes l: "l < length (snd ic)"

shows "R ic p l t \<preceq> 2^c - 1"
proof -
  have a: "R ic p l t \<le> 2^c - 1" using cells_bounded less_Suc_eq_le
    using l by fastforce
  have b: "r < c \<Longrightarrow> nth_bit (2^c - 1) r = 1" for r
    apply (auto simp: nth_bit_def)
    apply (subst dmask_aux)
    apply (auto)
    by (metis Suc_pred dvd_power even_Suc mod_0_imp_dvd not_mod2_eq_Suc_0_eq_0
              zero_less_diff zero_less_numeral zero_less_power)
  show ?thesis using lt_implies_mask cells_bounded l
    by (auto) (metis One_nat_def b)
qed

lemma lm04_15_register_masking:
  fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat

defines "b == B c"
defines "d == D q c b"

assumes cells_bounded: "cells_bounded ic p c"
assumes l: "l < length (snd ic)"

defines "r == RLe ic p b q"

shows "r l \<preceq> d"
proof -
  have "\<And>t. R ic p l t \<preceq> 2^c - 1" using cells_bounded l
    by (rule register_cells_masked)
  hence rmasked: "\<forall>t. R ic p l t \<preceq> 2^c - 1"
    by (intro allI)

  have rlt: "\<forall>t. R ic p l t \<le> 2^c - 1"
    using cells_bounded less_Suc_eq_le l by fastforce

  have rlmasked: "(\<Sum>t = 0..q. R ic p l t * b^t) \<preceq> (\<Sum>t = 0..q. (2^c - 1) * b^t)"
    using rmasked rlt b_def B_def mask_conserved_sum by (auto)

  thus ?thesis
    by (auto simp: r_def d_def D_def RLe_def mult.commute cong: sum.cong)
qed

(* ZERO INDICATORS *)
lemma zero_cells_masked:
  fixes l :: register
    and t :: nat
    and ic :: configuration
    and p :: program

assumes l: "l < length (snd ic)"

shows "Z ic p l t \<preceq> 1"
proof -
  have "nth_bit 1 0 = 1" by (auto simp: nth_bit_def)
  thus ?thesis apply (auto) apply (rule lt_implies_mask)
    by (metis (full_types) One_nat_def Suc_1 Z_bounded less_Suc_eq_le less_one power_one_right)
qed

lemma lm04_15_zero_masking:
  fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat

defines "b == B c"
defines "e == E q b"

assumes cells_bounded: "cells_bounded ic p c"
assumes l: "l < length (snd ic)"
assumes c: "c > 0"

defines "z == ZLe ic p b q"

shows "z l \<preceq> e"
proof -
  have "\<And>t. Z ic p l t \<preceq> 1" using l
    by (rule zero_cells_masked)
  hence zmasked: "\<forall>t. Z ic p l t \<preceq> 1"
    by (intro allI)

  have zlt: "\<forall>t. Z ic p l t \<le> 2 ^ c - 1"
    using cells_bounded less_Suc_eq_le by fastforce

  have 1: "(1::nat) \<le> 2 ^ c - 1" using c
    by (simp add: Nat.le_diff_conv2 numeral_2_eq_2 self_le_power)

  have rlmasked: "(\<Sum>t = 0..q. Z ic p l t * b^t) \<preceq> (\<Sum>t = 0..q. 1 * b^t)"
    using zmasked zlt 1 b_def B_def mask_conserved_sum[of "Z ic p l" 1]
    by (auto)

  thus ?thesis
    by (auto simp: z_def e_def E_def ZLe_def mult.commute cong: sum.cong)
qed

(* Relation between zero indicator and register *)
lemma lm04_19_zero_register_relations:
  fixes c :: nat
    and l :: register
    and t :: nat
    and ic :: configuration
    and p :: program

assumes cells_bounded: "cells_bounded ic p c"
assumes l: "l < length (snd ic)"

defines "z == Z ic p"
defines "r == R ic p"

shows "2^c * z l t = (r l t + 2^c - 1) && 2^c"
proof -
  have a1: "R ic p l t \<noteq> 0 \<Longrightarrow> 2^c \<le> R ic p l t + 2^c - 1"
    by auto
  have a2: "R ic p l t + 2^c - 1 < 2^Suc c" using cells_bounded
    by (simp add: l less_imp_diff_less)

  have "Z ic p l t = nth_bit (R ic p l t + 2^c - 1) c"
    apply (cases "R ic p l t = 0")
    subgoal by (auto simp add: Z_def R_def nth_bit_def)
    subgoal using cells_bounded bitAND_single_digit a1 a2 Z_def
      by auto
    done

  also have "2^c * nth_bit (R ic p l t + 2^c - 1) c = ((R ic p l t + 2^c - 1) && 2^c)"
    using nth_digit_bitAND_equiv by auto

  finally show ?thesis by (auto simp: z_def r_def)
qed

lemma lm04_20_zero_definition:
  fixes c :: nat
    and l :: register
    and ic :: configuration
    and p :: program
    and q :: nat

defines "b == B c"
defines "f == F q c b"
defines "d == D q c b"

assumes cells_bounded: "cells_bounded ic p c"
assumes l: "l < length (snd ic)"

assumes c: "c > 0"

defines "z == ZLe ic p b q"
defines "r == RLe ic p b q"

shows "2^c * z l = (r l + d) && f"
proof -
  have "\<And>t. 2^c * Z ic p l t = (R ic p l t + 2^c - 1) && 2^c"
    by (rule lm04_19_zero_register_relations cells_bounded l) +
  hence raw_sums: "(\<Sum>t = 0..q. 2^c * Z ic p l t * b^t) 
                 = (\<Sum>t = 0..q. ((R ic p l t + 2^c - 1) && 2^c) * b^t)"
    by auto

  have "(\<Sum>t = 0..q. 2^c * Z ic p l t * b^t) = 2^c * (\<Sum>t = 0..q. Z ic p l t * b^t)"
    by (auto simp: sum_distrib_left mult.assoc cong: sum.cong)
  also have "... = 2^c * z l"
    by (auto simp: z_def ZLe_def mult.commute)
  finally have lhs: "(\<Sum>t = 0..q. 2^c * Z ic p l t * b^t) = 2^c * z l"
    by auto

  have "(\<Sum>t = 0..q. (R ic p l t + (2^c - 1)) * b^t) 
      = (\<Sum>t = 0..q. R ic p l t * b^t + (2^c - 1) * b^t)"
    apply (rule sum.cong)
    apply (auto simp: add.commute mult.commute)
    subgoal for x using distrib_left[of "b^x" "R ic p l x" "2^c - 1"] by (auto simp: algebra_simps)
    done
  also have "... = (\<Sum>t = 0..q. (R ic p l t * b^t)) + (\<Sum>t = 0..q. (2^c - 1) * b^t)"
    by (rule sum.distrib)
  also have "... = r l + d"
    by (auto simp: r_def RLe_def d_def D_def mult.commute)
  finally have split_sums: "(\<Sum>t = 0..q. (R ic p l t + (2^c - 1)) * b^t) = r l + d"
    by auto

  have a1: "(2::nat) ^ c < (2::nat) ^ Suc c - 1" using c by (induct c, auto, fastforce)
  have a2: "\<forall>t. R ic p l t + 2 ^ c - 1 \<le> 2 ^ Suc c" using cells_bounded B_def
    by (simp add: less_imp_diff_less l) (simp add: Suc_leD l less_imp_le_nat numeral_Bit0)
  have "(\<Sum>t = 0..q. ((R ic p l t + 2^c - 1) && 2^c) * b^t)
      = (\<Sum>t = 0..q. (R ic p l t + 2^c - 1) * b^t) && (\<Sum>t = 0..q. 2^c * b^t)"
    using bitAND_linear_sum[of "\<lambda>t. R ic p l t + 2^c - 1" "c" "\<lambda>t. 2^c"]
          cells_bounded b_def B_def a1 a2
    apply auto
    by (smt One_nat_def Suc_less_eq Suc_pred a1 add.commute add_gr_0 l mult_2 
        nat_add_left_cancel_less power_Suc zero_less_numeral zero_less_power)
  also have "... = (\<Sum>t = 0..q. (R ic p l t + 2^c - 1) * b^t) && f"
    by (auto simp: f_def F_def)
  also have "... = (r l + d) && f" using split_sums
    by auto
  finally have rhs: "(\<Sum>t = 0..q. ((R ic p l t + 2^c - 1) && 2^c) * b^t) = (r l + d) && f"
    by auto

  show ?thesis using raw_sums lhs rhs
    by auto
qed

lemma state_mask:
fixes c :: nat
  and l :: register
  and ic :: configuration
  and p :: program
  and q :: nat
  and a :: nat

defines "b \<equiv> B c"
    and "m \<equiv> length p - 1"

defines "e \<equiv> E q b"

assumes is_val: "is_valid_initial ic p a"
    and q: "q > 0"
    and "c > 0"

assumes terminate: "terminates ic p q"
  shows "SKe ic p b q k \<preceq> e"
proof -
  have "1 \<le> 2 ^ c - Suc 0" using \<open>c>0\<close> by (metis One_nat_def Suc_leI one_less_numeral_iff 
                                           one_less_power semiring_norm(76) zero_less_diff)
  have Smask: "S ic p k t \<preceq> 1" for t by (simp add: S_def)
  have Sbound: "S ic p k t \<le> 2 ^ c - Suc 0" for t using \<open>1\<le>2^c-Suc 0\<close> by (simp add: S_def)
  have rlmasked: "(\<Sum>t = 0..q. S ic p k t * b^t) \<preceq> (\<Sum>t = 0..q. 1 * b^t)"
    using b_def B_def Smask Sbound mask_conserved_sum[of "S ic p k" 1] \<open>1 \<le> 2^c-Suc 0\<close> by auto

  thus ?thesis using SKe_def e_def E_def by (auto simp: mult.commute)
qed

lemma state_sum_mask:
fixes c :: nat
  and l :: register
  and ic :: configuration
  and p :: program
  and q :: nat
  and a :: nat

defines "b \<equiv> B c"
    and "m \<equiv> length p - 1"

defines "e \<equiv> E q b"

assumes is_val: "is_valid_initial ic p a"
    and q: "q > 0"
    and "c > 0"
    and "b > 1"

assumes "M\<le>m"

assumes terminate: "terminates ic p q"
shows "(\<Sum>k\<le>M. SKe ic p b q k) \<preceq> e"
proof -
  have e_aux: "nth_digit e t b = (if t\<le>q then 1 else 0)" for t
    unfolding e_def E_def b_def B_def
    using `b>1` b_def nth_digit_gen_power_series[of "\<lambda>k. Suc 0" "c" "q"]
    by (auto simp: b_def B_def)

  have state_unique: "\<forall>k\<le>m. S ic p k t = 1 \<longrightarrow> (\<forall>j\<noteq>k. S ic p j t = 0)" for t
    using S_def by (induction t, auto)

  have h1: "\<forall>t. nth_digit (\<Sum>k\<le>M. SKe ic p b q k) t b \<le> (if t\<le>q then 1 else 0)"
  proof - {
      fix t
      have aux_bound_1: "(\<Sum>k\<le>M. S ic p k t') \<le> 1" for t'
      proof (cases "\<exists>k\<le>M. S ic p k t' = 1")
        case True
        then obtain k where k: "k\<le>M \<and> S ic p k t' = 1" by auto
        moreover have "\<forall>j\<le>M. j \<noteq> k \<longrightarrow> S ic p j t' = 0"
          using state_unique `M<=m` k S_def
          by (auto) (presburger)
        ultimately have "(\<Sum>k\<le>M. S ic p k t') = 1"
          using S_def by auto
        then show ?thesis
          by auto
      next
        case False
        then show ?thesis using S_bounded
          by (auto) (metis (no_types, lifting) S_def atMost_iff eq_imp_le le_SucI sum_nonpos)
      qed
      hence aux_bound_2: "\<And>t'. (\<Sum>k\<le>M. S ic p k t') < 2^c"
        by (metis Suc_1 `c>0` le_less_trans less_Suc_eq one_less_power)

      have h2: "(\<Sum>k\<le>M. SKe ic p b q k) = (\<Sum>t = 0..q. \<Sum>k\<le>M. b ^ t * S ic p k t)"
        unfolding SKe_def using sum.swap by auto
      hence "(\<Sum>k\<le>M. SKe ic p b q k) = (\<Sum>t = 0..q. b^t * (\<Sum>k\<le>M. S ic p k t))"
        unfolding SKe_def by (simp add: sum_distrib_left)

      hence "nth_digit (\<Sum>k\<le>M. SKe ic p b q k) t b = (if t\<le>q then (\<Sum>k\<le>M. S ic p k t) else 0)"
        using `c>0` aux_bound_2 h2 unfolding SKe_def
        using nth_digit_gen_power_series[of "\<lambda>t. (\<Sum>k\<le>M. S ic p k t)" "c" "q" "t"]
        by (smt B_def Groups.mult_ac(2) assms(7) aux_bound_1 b_def le_less_trans sum.cong)
      hence "nth_digit (\<Sum>k\<le>M. SKe ic p b q k) t b \<le> (if t\<le>q then 1 else 0)"
        using aux_bound_1 by auto
    } thus ?thesis by auto
  qed
  moreover have "\<forall>t>q. nth_digit (\<Sum>k\<le>M. SKe ic p b q k) t b = 0"
    by (metis (full_types) h1 le_0_eq not_less)
  ultimately have "\<forall>t. \<forall>i<Suc c. nth_digit (\<Sum>k\<le>M. SKe ic p b q k) t b \<exclamdown> i
                          \<le> nth_digit e t b \<exclamdown> i" 
    using aux_lt_implies_mask linorder_neqE_nat e_aux
    by (smt One_nat_def le_0_eq le_SucE less_or_eq_imp_le nat_zero_less_power_iff
            numeral_2_eq_2 zero_less_Suc)

  hence "\<forall>t. \<forall>i<Suc c. (\<Sum>k\<le>M. SKe ic p b q k) \<exclamdown> (Suc c * t + i) \<le> e \<exclamdown> (Suc c * t + i)"
    using digit_gen_pow2_reduct[where ?c = "Suc c" and ?a = "(\<Sum>k\<le>M. SKe ic p b q k)"]
    using digit_gen_pow2_reduct[where ?c = "Suc c" and ?a = e]
    by (simp add: b_def B_def)
  moreover have "\<forall>j. \<exists>t i. i < Suc c \<and> j = (Suc c * t + i)"
    using mod_less_divisor zero_less_Suc
    by (metis add.commute mod_mult_div_eq)
  ultimately have "\<forall>j. (\<Sum>k\<le>M. SKe ic p b q k) \<exclamdown> j \<le> e \<exclamdown> j"
    by metis
 
  thus ?thesis
    using masks_leq_equiv by auto
qed

end
