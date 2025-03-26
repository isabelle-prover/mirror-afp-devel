theory Theta_Functions_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Computational_Algebra.Computational_Algebra"
begin

subsection \<open>Miscellanea\<close>

(* some rules to simplify away annoying things like "1/2 \<in> \<int>" *)
lemma fraction_numeral_not_in_Ints [simp]:
  assumes "\<not>(numeral b :: int) dvd numeral a"
  shows   "numeral a / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" "numeral a", where ?'a = 'a] assms by simp

lemma fraction_numeral_not_in_Ints' [simp]:
  assumes "b \<noteq> Num.One"
  shows   "1 / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" 1, where ?'a = 'a] assms by simp

lemmas [simp] = not_in_Ints_imp_not_in_nonpos_Ints minus_in_Ints_iff

lemma is_square_mult_prime_left_iff:
  assumes "prime p"
  shows   "is_square (p * x) \<longleftrightarrow> p dvd x \<and> is_square (x div p)"
proof
  assume *: "p dvd x \<and> is_square (x div p)"
  have [simp]: "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "x = y ^ 2 * p"
    by (auto elim!: dvdE is_nth_powerE simp: mult_ac)
  have "is_square ((p * y) ^ 2)"
    by auto
  also have "(p * y) ^ 2 = p * x"
    by (simp add: y power2_eq_square algebra_simps)
  finally show "is_square (p * x)" .
next
  assume *: "is_square (p * x)"
  have "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "p * x = y ^ 2"
    by (elim is_nth_powerE)
  have "p dvd y ^ 2"
    by (simp flip: y)
  hence "p dvd y"
    using \<open>prime p\<close> using prime_dvd_power by blast
  then obtain z where z: "y = p * z "
    by (elim dvdE)
  have "p * x = p * (p * z ^ 2)"
    by (simp add: y z algebra_simps power2_eq_square)
  hence x_eq: "x = p * z ^ 2"
    using \<open>p \<noteq> 0\<close> by simp
  show "p dvd x \<and> is_square (x div p)"
    using \<open>p \<noteq> 0\<close> by (simp add: x_eq)
qed

lemma is_square_mult2_nat_iff:
  "is_square (2 * b :: nat) \<longleftrightarrow> even b \<and> is_square (b div 2)"
  by (rule is_square_mult_prime_left_iff) auto

lemma is_square_mult2_int_iff:
  "is_square (2 * b :: int) \<longleftrightarrow> even b \<and> is_square (b div 2)"
  by (rule is_square_mult_prime_left_iff) auto

lemma is_nth_power_mult_cancel_left:
  fixes a b :: "'a :: semiring_gcd"
  assumes "is_nth_power n a" "a \<noteq> 0"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n b"
proof (cases "n > 0")
  case True
  show ?thesis
  proof
    assume "is_nth_power n (a * b)"
    then obtain x where x: "a * b = x ^ n"
      by (elim is_nth_powerE)
    obtain y where y: "a = y ^ n"
      using assms by (elim is_nth_powerE)
    have "y ^ n dvd x ^ n"
      by (simp flip: x y)
    hence "y dvd x"
      using \<open>n > 0\<close> by simp
    then obtain z where z: "x = y * z"
      by (elim dvdE)
    have "x ^ n = y ^ n * z ^ n"
      by (simp add: z power_mult_distrib)
    hence "b = z ^ n"
      using \<open>a \<noteq> 0\<close> by (simp flip: x y)
    thus "is_nth_power n b"
      by auto
  qed (use assms in \<open>auto intro: is_nth_power_mult\<close>)
qed (use assms in auto)

lemma is_nth_power_mult_cancel_right:
  fixes a b :: "'a :: semiring_gcd"
  assumes "is_nth_power n b" "b \<noteq> 0"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n a"
  by (subst mult.commute, subst is_nth_power_mult_cancel_left) (use assms in auto)

end