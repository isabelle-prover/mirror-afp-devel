theory Lemma_4_4
  imports Lucas_Sequences HOL.Real
begin

subsection \<open>Bounds on expressions involving Lucas Sequences\<close>

lemma bernoulli_ineq:
  fixes a::int and n::nat
  assumes "a \<ge> 1"
  shows "(a-1)^(Suc n) \<ge> a^(Suc n) - int (n+1)*a^n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note t = this
  have triv: "int (n+1) * a^n \<ge> 0" using assms by auto
  have "(a-1)^(Suc (Suc n)) = (a-1) * (a-1)^(Suc n)" by auto
  hence "(a-1)^(Suc (Suc n)) \<ge> (a-1) * (a^(Suc n) - int (n+1)*a^n)"
    using assms t mult_left_mono[of "(a^(Suc n) - int (n+1)*a^n)" "(a-1)^(Suc n)" "a-1"] by auto
  hence "(a-1)^(Suc (Suc n)) \<ge> a^(Suc (Suc n)) - int (Suc n +1)*a^(Suc n) + int (n+1)*a^n"
    by (auto simp add: algebra_simps)
  thus ?case using triv by force
qed

lemma lemma_4_4:
  fixes U::int and V::int and X::nat
  assumes "U \<ge> 2*int X" and "V \<ge> 1" and "X \<ge> 1"
  shows "-2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)
      \<le> U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))
    \<and> U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))
      \<le> 2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"
proof -
  (* First bounds - consequences from 3.1.3 *)

  have minU: "U \<ge> 2" using assms by auto
  have min_UV: "U*(V+1) > 1" using assms by (smt (verit) int_ops(2) less_1_mult of_nat_mono)
  hence "Suc (Suc (2*X-1)) = 2*X+1 \<and> 2*X-1+1 = 2*X \<and> 1 < U*(V+1)" using assms by auto
  hence min_2: "\<psi> (U*(V+1)) (2*X+1) \<ge> (U*(V+1)-1)^(2*X)"
    using lucas_exp_growth_gt[of "U*(V+1)" "2*X-1"] by auto
  have "Suc (Suc (Suc (2*X-2))) = 2*X+1 \<and> 2*X-2+2 = 2*X" using assms by auto
  hence maj_2: "\<psi> (U*(V+1)) (2*X+1) \<le> (U*(V+1))^(2*X)"
    using lucas_exp_growth_lt[of "U*(V+1)" "2*X-2"] min_UV by auto
  have minU2V: "U^2*V > 1"
    using assms minU less_1_mult mult.right_neutral one_add_one power2_eq_square
        verit_comp_simplify1(3) verit_la_disequality
    by (metis less_iff_succ_less_eq)
  hence min_1: "\<psi> (U^2*V) (X+1) \<ge> (U^2*V-1)^X"
    using lucas_exp_growth_gt[of "U^2*V" "X-1"] assms by auto
  have maj_1: "\<psi> (U^2*V) (X+1) \<le> (U^2*V)^X"
    using lucas_exp_growth_le[of "U^2*V" "X-1"] assms minU2V by auto
  have pos_1: "\<psi> (U^2*V) (X+1) > 0" using lucas_strict_monotonicity[of "U^2*V" X] assms minU2V by auto
  have pos_2: "\<psi> (U*(V+1)) (2*X+1) > 0" using lucas_strict_monotonicity[of "U*(V+1)" "2*X"] min_UV assms by auto

  (* First inequality *)

  have ineq1: "(U*(V+1)-1)^(2*X) * \<psi> (U^2*V) (X+1) \<le> \<psi> (U*(V+1)) (2*X+1) * (U^2*V)^X"
    using maj_1 min_2 pos_1 pos_2 mult_mono[of "(U*(V+1)-1)^(2*X)"
        "\<psi> (U*(V+1)) (2*X+1)" "\<psi> (U^2*V) (X+1)" "(U^2*V)^X"] by auto
  have "(U*(V+1)-1)^(2*X) * \<psi> (U^2*V) (X+1)
      \<ge> ((U*(V+1))^(2*X) - 2*int X*(U*(V+1))^(2*X-1)) * \<psi> (U^2*V) (X+1)"
    using pos_1 bernoulli_ineq[of "U*(V+1)" "2*X-1"] assms min_UV by auto
  hence "\<psi> (U*(V+1)) (2*X+1) * (U^2*V)^X
      \<ge> ((U*(V+1))^(2*X) - 2*int X*(U*(V+1))^(2*X-1)) * \<psi> (U^2*V) (X+1)"
    using ineq1 by auto
  hence ineq2: "\<psi> (U*(V+1)) (2*X+1) * (U^2*V)^X - (U*(V+1))^(2*X) * \<psi> (U^2*V) (X+1)
      \<ge> - 2*int X*(U*(V+1))^(2*X-1) * \<psi> (U^2*V) (X+1)"
    using diff_mono[of "((U*(V+1))^(2*X) - 2*int X*(U*(V+1))^(2*X-1)) * \<psi> (U^2*V) (X+1)"
        "\<psi> (U*(V+1)) (2*X+1) * (U^2*V)^X" "(U*(V+1))^(2*X) * \<psi> (U^2*V) (X+1)"
        "(U*(V+1))^(2*X) * \<psi> (U^2*V) (X+1)"] by (auto simp add: algebra_simps)
  have fact1: "(U^2*V)^X = U^(2*X)*V^X" by (simp add: power_mult power_mult_distrib)
  have fact2: "U^(2*X) = U*U^(2*X-1)" 
    using assms semiring_normalization_rules(27)[of U "2*X-1"] by auto
  hence "(U^2*V)^X = U^(2*X-1)*U*V^X" using fact1 by auto
  hence fact3: "\<psi> (U*(V+1)) (2*X+1) * (U^2*V)^X = U^(2*X-1)*U*V^X * \<psi> (U*(V+1)) (2*X+1)"
    using assms by (auto simp add: algebra_simps)
  have "(U*(V+1))^(2*X) * \<psi> (U^2*V) (X+1) = U^(2*X-1)*U*(V+1)^(2*X)* \<psi> (U^2*V) (X+1)"
    using fact2 power_mult_distrib[of U "V+1" "2*X"] by auto
  hence fact4: "\<psi> (U*(V+1)) (2*X+1) * (U^2*V)^X - (U*(V+1))^(2*X) * \<psi> (U^2*V) (X+1) =
      U^(2*X-1)*U*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))"
    using fact3 by (auto simp add: algebra_simps)
  have "-2*int X*(U*(V+1))^(2*X-1) * \<psi> (U^2*V) (X+1)
      = U^(2*X-1) * (- 2*int X * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1))"
    using power_mult_distrib[of U "V+1" "2*X-1"] by (auto simp add: algebra_simps)
  hence ineq3: "U^(2*X-1)*U*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))
      \<ge> U^(2*X-1) * (- 2*int X * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1))"
    using ineq2 fact4 by argo
  have "U^(2*X-1) > 0" using assms by auto
  hence fact5: "U^(2*X-1)*b \<ge> U^(2*X-1)*c \<Longrightarrow> b \<ge> c" for b and c
    by simp
  have "U*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))
      \<ge> - 2*int X * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1)"
    using ineq3 fact5[of "U*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))"
        "- 2*int X * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1)"] by (metis (no_types, lifting) fact5 mult.assoc)
  hence ineq4: "U*V*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))
      \<ge> -2*int X * V * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1)"
    using assms mult_left_mono[of"- 2*int X * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1)" 
        "U*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))" V]
    by (auto simp add: algebra_simps)
  have "2*int X * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1) \<ge> 0" using assms pos_1 by auto
  hence fact6: "-2*int X * V * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1)
      \<ge> -2*int X * (V+1) * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1)"
    using assms by (auto simp add: algebra_simps)
  have "(V+1)*(V+1)^(2*X-1) = (V+1)^(2*X)"
    using assms semiring_normalization_rules(27)[of "V+1" "2*X-1"] by auto
  hence "-2*int X * (V+1) * (V+1)^(2*X-1) * \<psi> (U^2*V) (X+1) = -2*int X * (V+1)^(2*X) * \<psi> (U^2*V) (X+1)"
    by auto
  hence ineq5: "U*V*(V^X * \<psi> (U*(V+1)) (2*X+1) - (V+1)^(2*X)* \<psi> (U^2*V) (X+1))
      \<ge> -2*int X * (V+1)^(2*X) * \<psi> (U^2*V) (X+1)"
    using fact6 ineq4 by (auto simp add: algebra_simps)

(* Second inequality *)

  have ineq6: "(U^2*V-1)^X * \<psi> (U*(V+1)) (2*X+1) \<le> \<psi> (U^2*V) (X+1) * (U*(V+1))^(2*X)"
    using mult_mono[of "(U^2*V-1)^X" "\<psi> (U^2*V) (X+1)" "\<psi> (U*(V+1)) (2*X+1)" "(U*(V+1))^(2*X)"]
      maj_2 min_1 pos_1 pos_2 by auto
  have fact7: "(U^2*V+2*int X)*(U^2*V-1)^X \<ge> (U^2*V+2*int X)*((U^2*V)^X - int X * (U^2*V)^(X-1))"
    using bernoulli_ineq[of "U^2*V" "X-1"] minU2V assms(3) by auto
  have "Suc (X-1) = X" using assms(3) by auto
  hence "(U^2*V)^X = U^2*V*(U^2*V)^(X-1)" by (metis power_Suc)
  hence "((U^2*V)^X - int X * (U^2*V)^(X-1)) = (U^2*V-int X)*(U^2*V)^(X-1)"
    by (auto simp add: algebra_simps)
  hence fact8: "(U^2*V+2*int X)*(U^2*V-1)^X \<ge> (U^2*V+2*int X)*(U^2*V-int X)*(U^2*V)^(X-1)"
    using fact7 by auto
  have fact9: "(U^2*V+2*int X)*(U^2*V-int X) = (U^2*V)^2 + int X*(U^2*V - 2*int X)"
    by (auto simp add: algebra_simps power2_eq_square)
  have "U*V \<ge> 1" using assms(2) minU by (metis dual_order.strict_trans2 less_1_mult mult.left_neutral
 mult.right_neutral not_le_imp_less not_less_iff_gr_or_eq not_numeral_less_one)
  hence "U^2*V \<ge> 2*int X" using assms power2_eq_square[of U] mult_mono[of "2*int X" U 1 "U*V"] by auto
  hence "(U^2*V)^2 + int X*(U^2*V - 2*int X) \<ge> (U^2*V)^2" using assms by auto
  hence fact10: "(U^2*V+2*int X)*(U^2*V-int X) \<ge> (U^2*V)^2" using fact9 by auto
  have "(U^2*V)^(X-1) \<ge> 0" using minU2V by auto
  hence "(U^2*V+2*int X)*(U^2*V-1)^X \<ge> (U^2*V)^2 * (U^2*V)^(X-1)"
    using fact8 fact10 mult_right_mono[of "(U^2*V)^2" "(U^2*V+2*int X)*(U^2*V-int X)" "(U^2*V)^(X-1)"]
    by auto
  hence ineq7: "(U^2*V+2*int X)*(U^2*V-1)^X * \<psi> (U*(V+1)) (2*X+1)
      \<ge> (U^2*V)^2 * (U^2*V)^(X-1)*\<psi> (U*(V+1)) (2*X+1)"
    using pos_2 mult_right_mono[of "(U^2*V)^2 * (U^2*V)^(X-1)" "(U^2*V+2*int X)*(U^2*V-1)^X" "\<psi> (U*(V+1)) (2*X+1)"]
    by auto
  have "(U^2*V)^2*(U^2*V)^(X-1) = U^(2*X)*V^X*U^2*V" 
    using power_add[of "U^2*V" 2 "X-1"] power_add[of "U^2*V" X 1] power_mult_distrib[of "U^2" V X]
      power_mult[of U 2 X] assms(3) by auto
  hence ineq8: "(U^2*V+2*int X)*(U^2*V-1)^X * \<psi> (U*(V+1)) (2*X+1)
      \<ge> U^(2*X)*V^X * U^2*V * \<psi> (U*(V+1)) (2*X+1)"
    using ineq7 by auto
  have "U^2*V+2*int X \<ge> 0" using assms minU2V by auto
  hence "(U^2*V+2*int X) * \<psi> (U^2*V) (X+1) * (U*(V+1))^(2*X)
      \<ge> (U^2*V+2*int X)*(U^2*V-1)^X * \<psi> (U*(V+1)) (2*X+1)"
    using ineq6 mult_left_mono[of "(U^2*V-1)^X * \<psi> (U*(V+1)) (2*X+1)" "\<psi> (U^2*V) (X+1) * (U*(V+1))^(2*X)" "U^2*V+2*int X"]
    by auto
  hence ineq9: "(U^2*V+2*int X) * \<psi> (U^2*V) (X+1) * (U*(V+1))^(2*X)
      \<ge> V^X * U^2*V * \<psi> (U*(V+1)) (2*X+1)*U^(2*X)"
    using ineq8 by (auto simp add: algebra_simps)
  have "(U*(V+1))^(2*X) = (V+1)^(2*X)*U^(2*X)" using power_mult_distrib[of U "V+1" "2*X"] by auto
  hence ineq10: "(U^2*V+2*int X) * \<psi> (U^2*V) (X+1) * (V+1)^(2*X)*U^(2*X)
      \<ge> V^X * U^2*V * \<psi> (U*(V+1)) (2*X+1)*U^(2*X)" using ineq9 by auto
  have "U^(2*X) > 0" using minU by auto
  hence "a*U^(2*X) \<le> b*U^(2*X) \<Longrightarrow> a \<le> b" for a and b by simp
  hence "(U^2*V+2*int X) * \<psi> (U^2*V) (X+1) * (V+1)^(2*X) \<ge> V^X * U^2*V * \<psi> (U*(V+1)) (2*X+1)"
    using ineq10 by auto
  hence ineq11: "2*int X * \<psi> (U^2*V) (X+1) *(V+1)^(2*X)
      \<ge> U^2*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))"
    using diff_mono[of "V^X * U^2*V * \<psi> (U*(V+1)) (2*X+1)" "(U^2*V+2*int X) * \<psi> (U^2*V) (X+1) * (V+1)^(2*X)"
        "U^2*V*(V+1)^(2*X) * \<psi> (U^2*V) (X +1)" "U^2*V*(V+1)^(2*X) * \<psi> (U^2*V) (X +1)"]
    by (auto simp add: algebra_simps)
  have "2*int X * \<psi> (U^2*V) (X+1) *(V+1)^(2*X) \<ge> 0" using assms(3) pos_1 by auto
  hence "2*int X * \<psi> (U^2*V) (X+1) *(V+1)^(2*X) \<le> U* 2*int X * \<psi> (U^2*V) (X+1) *(V+1)^(2*X)"
    using minU mult_right_mono[of 1 U "2*int X * \<psi> (U^2*V) (X+1) *(V+1)^(2*X)"] by auto
  hence ineq12: "U* (2*int X  * (V+1)^(2*X))* \<psi> (U^2*V) (X+1)
      \<ge> U*(U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1)))"
    using ineq11 power2_eq_square[of U] by (auto simp add: algebra_simps)
  have fact11: "U*a \<ge> U*b \<Longrightarrow> a \<ge> b" for a and b using minU by auto
  have "U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))
      \<le> 2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"
    using ineq12 fact11[of "U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))"
        "2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"] by auto

  thus ?thesis using ineq5 by auto
qed

text \<open>Corollaries of lemma 3.9 easier to handle for the proof of Theorem 2\<close>

lemma lemma_4_4_cor:
  fixes U::int and V::int and X::nat
  assumes "U \<ge> 2*int X" and "V \<ge> 1" and "X \<ge> 1"
  shows "abs (U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X+1)))
    \<le> 2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"
  using assms lemma_4_4
 mult_minus_left by fastforce

text \<open>This version condenses all inequalities using absolute values\<close>

lemma lemma_4_4_abs:
  fixes U::int and V::int and X::nat
  assumes "abs U \<ge> 2*int X" and "V \<ge> 1" and "X \<ge> 1"
  shows "-2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)
          \<le> abs U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))
     \<and> abs U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))
        \<le> 2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"
proof -
  have even: "\<psi> (abs U*(V+1)) (2*X +1) = \<psi> (U*(V+1)) (2*X +1)"
    using assms lucas_symmetry_A[of "abs U * (V+1)" "2*X+1"]
    by (smt (z3) abs_zmult_eq_1 dvd_triv_left even_plus_one_iff mult_minus_left of_nat_1 of_nat_le_iff zero_le_mult_iff)
  have "-2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)
        \<le> abs U*V*(V^X * \<psi> (abs U*(V+1)) (2*X+1) - (V+1)^(2*X) * \<psi> ((abs U)^2*V) (X+1))
      \<and> abs U*V*(V^X * \<psi> (abs U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> ((abs U)^2*V) (X +1))
        \<le> 2*int X*(V+1)^(2*X)*\<psi> ((abs U)^2*V) (X+1)"
    using lemma_4_4
  [of X "abs U" V] assms by simp
  then show ?thesis using even by simp
qed

lemma lemma_4_4_cor_abs:
  fixes U::int and V::int and X::nat
  assumes "abs U \<ge> 2*int X" and "V \<ge> 1" and "X \<ge> 1"
  shows "abs (U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X+1)))
        \<le> 2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"
  using assms lemma_4_4_abs mult_minus_left by fastforce

text \<open>This version uses \<open>\<rho>\<close> (defined in the lemma)\<close>

lemma lemma_4_4_cor_rho:
  fixes U::int and V::int and X::nat and \<rho>::real
  assumes "U \<ge> 2*int X" and "V \<ge> 1" and "X \<ge> 1"
  defines "\<rho> \<equiv> (real_of_int (V+1)^(2*X))/(real_of_int V^X)"
  shows "abs (\<psi> (U*(V+1)) (2*X +1)/ \<psi> (U^2*V) (X +1) - \<rho>) \<le> 2*int X*\<rho> / (U*V)"
proof -
  define u v x where uvx_def: "u = real_of_int U" "v = real_of_int V" "x = real_of_nat X"
  have "u*v*(v^X * real_of_int (\<psi> (U*(V+1)) (2*X +1)) - (v+1)^(2*X) * real_of_int (\<psi> (U^2*V) (X +1))) 
    = real_of_int (U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1)))"
    using uvx_def by auto
  hence eq1: "abs (u*v*(v^X * real_of_int (\<psi> (U*(V+1)) (2*X +1))
    - (v+1)^(2*X) * real_of_int (\<psi> (U^2*V) (X +1)))) 
    = real_of_int (abs (U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1))))"
    by auto
  have eq2: "real_of_int (2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1))
    = 2*x*(v+1)^(2*X)*real_of_int (\<psi> (U^2*V) (X+1))"
    using uvx_def by auto 
  have "abs (U*V*(V^X * \<psi> (U*(V+1)) (2*X +1) - (V+1)^(2*X) * \<psi> (U^2*V) (X +1)))
    \<le> 2*int X*(V+1)^(2*X)*\<psi> (U^2*V) (X+1)"
    using lemma_4_4_cor assms by auto
  hence ineq: "abs (u*v*(v^X * real_of_int (\<psi> (U*(V+1)) (2*X +1))
    - (v+1)^(2*X) * real_of_int (\<psi> (U^2*V) (X +1))))
    \<le> 2*x*(v+1)^(2*X)*real_of_int (\<psi> (U^2*V) (X+1))"
    using eq1 eq2 by (metis of_int_le_iff)
  have \<rho>_def: "(v+1)^(2*X) = v^X*\<rho>" using assms uvx_def by auto
  from ineq have ineq2: "abs (u*v*(v^X*real_of_int (\<psi> (U*(V+1)) (2*X+1))
    - (v^X*\<rho>)*real_of_int (\<psi> (U^2*V) (X+1))))
    \<le> 2*x*(v^X*\<rho>)*real_of_int (\<psi> (U^2*V) (X+1))"
    using \<rho>_def by force
  have U2VBe2: "U^2*V \<ge> 2"
    using power2_eq_square[of U] mult_mono[of 2 U 1 U] mult_mono[of 2 "U*U" 1 V] assms by auto
  hence \<psi>_pos: "real_of_int (\<psi> (U^2*V) (X+1)) > 0"
    using assms lucas_monotone3[of "U^2*V" "X+1"] by auto
  hence fact: "real_of_int (\<psi> (U^2*V) (X+1))
    * (real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) 
    = real_of_int (\<psi> (U*(V+1)) (2*X+1))"
    by force
  have "real_of_int (\<psi> (U^2*V) (X+1))
    * ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>) 
    = real_of_int (\<psi> (U^2*V) (X+1)) * (real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1))))
    - real_of_int (\<psi> (U^2*V) (X+1))*\<rho>"
    using distrib_left[of "real_of_int (\<psi> (U^2*V) (X+1))"
        "(real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1))))" \<rho>]
    by argo
  hence "real_of_int (\<psi> (U^2*V) (X+1))
    * ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>) 
    = real_of_int (\<psi> (U*(V+1)) (2*X+1)) - real_of_int (\<psi> (U^2*V) (X+1))*\<rho>"
    using fact by auto
  hence eq1: "u*v*v^X*real_of_int (\<psi> (U^2*V) (X+1))
    * ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>) 
    = u*v*(v^X*real_of_int (\<psi> (U*(V+1)) (2*X+1)) - (v^X*\<rho>)*real_of_int (\<psi> (U^2*V) (X+1)))"
    by (auto simp add: algebra_simps)
  have ineqs_uvx: "u > 0 \<and> v > 0 \<and> v^X > 0" using assms uvx_def by auto
  hence "abs (u*v*v^X*real_of_int (\<psi> (U^2*V) (X+1))
    * ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>))
    = u*v*v^X*real_of_int (\<psi> (U^2*V) (X+1))
    * abs ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>)"
    using \<psi>_pos by (auto simp add: abs_mult)
  hence "u*v*v^X*real_of_int (\<psi> (U^2*V) (X+1))
    * abs ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>)
    \<le> 2*x*(v^X*\<rho>)*real_of_int (\<psi> (U^2*V) (X+1))"
    using eq1 ineq2 by argo
  hence "abs ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>)
    \<le> 2*x*\<rho>/(u*v)"
    using ineqs_uvx \<psi>_pos divide_right_mono[of "u*v*v^X*real_of_int (\<psi> (U^2*V) (X+1))
    * abs ((real_of_int (\<psi> (U*(V+1)) (2*X+1)) / (real_of_int (\<psi> (U^2*V) (X+1)))) - \<rho>)"
        "2*x*(v^X*\<rho>)*real_of_int (\<psi> (U^2*V) (X+1))" "u*v*v^X*real_of_int (\<psi> (U^2*V) (X+1))"] by auto
  then show ?thesis using uvx_def by auto
qed

text \<open>This version condenses all inequalities using absolute values, and uses \<open>\<rho>\<close>\<close>

lemma lemma_4_4_cor_rho_abs:
  fixes U::int and V::int and X::nat and \<rho>::real
  assumes "abs U \<ge> 2*int X" and "V \<ge> 1" and "X \<ge> 1"
  assumes "\<rho> \<equiv> (real_of_int (V+1)^(2*X))/(real_of_int V^X)"
  shows "abs (\<psi> (U*(V+1)) (2*X +1)/ \<psi> (U^2*V) (X+1) - \<rho>) \<le> 2*int X*\<rho> / (abs U*V)"
proof -
  have even: "\<psi> (abs U*(V+1)) (2*X +1) = \<psi> (U*(V+1)) (2*X +1)"
    using assms lucas_symmetry_A[of "abs U * (V+1)" "2*X+1"]
    by (smt (verit, best) dvd_triv_left even_plus_one_iff mult_minus_left zero_less_mult_iff zmult_eq_1_iff)
  have "abs (\<psi> (abs U*(V+1)) (2*X +1)/ \<psi> (U^2*V) (X +1) - \<rho>) \<le> 2*int X*\<rho> / (abs U*V)" 
    using lemma_4_4_cor_rho assms by fastforce
  then show ?thesis using even by simp
qed

end
