theory Theta_Functions_Library
imports
  "HOL-Computational_Algebra.Computational_Algebra" "HOL-Analysis.Analysis"
begin

lemma add_in_Ints_iff_left [simp]: "x \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  by (metis Ints_add Ints_diff add_diff_cancel_left')

lemma add_in_Ints_iff_right [simp]: "y \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  by (subst add.commute) auto

lemma diff_in_Ints_iff_left [simp]: "x \<in> \<int> \<Longrightarrow> x - y \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  by (metis Ints_diff add_in_Ints_iff_left diff_add_cancel)

lemma diff_in_Ints_iff_right [simp]: "y \<in> \<int> \<Longrightarrow> x - y \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  by (metis Ints_minus diff_in_Ints_iff_left minus_diff_eq)

lemmas [simp] = minus_in_Ints_iff

lemma of_int_div_of_int_in_Ints_iff:
  "(of_int n / of_int m :: 'a :: field_char_0) \<in> \<int> \<longleftrightarrow> m = 0 \<or> m dvd n"
proof
  assume *: "(of_int n / of_int m :: 'a) \<in> \<int>"
  {
    assume "m \<noteq> 0"
    from * obtain k where k: "(of_int n / of_int m :: 'a) = of_int k"
      by (auto elim!: Ints_cases)
    hence "of_int n = (of_int k * of_int m :: 'a)"
      using \<open>m \<noteq> 0\<close> by (simp add: field_simps)
    also have "\<dots> = of_int (k * m)"
      by simp
    finally have "n = k * m"
      by (subst (asm) of_int_eq_iff)
    hence "m dvd n" by auto
  }
  thus "m = 0 \<or> m dvd n" by blast
qed auto

lemma fraction_numeral_not_in_Ints [simp]:
  assumes "\<not>(numeral b :: int) dvd numeral a"
  shows   "numeral a / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" "numeral a", where ?'a = 'a] assms by simp

lemma fraction_numeral_not_in_Ints' [simp]:
  assumes "b \<noteq> Num.One"
  shows   "1 / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" 1, where ?'a = 'a] assms by simp

lemmas [simp] = not_in_Ints_imp_not_in_nonpos_Ints minus_in_Ints_iff

lemma of_int_div: "b dvd a \<Longrightarrow> of_int (a div b) = (of_int a / of_int b :: 'a :: field_char_0)"
  by auto
      
lemma is_square_mult_prime_left_iff:
  assumes "prime p"
  shows   "is_square (p * x) \<longleftrightarrow> p dvd x \<and> is_square (x div p)"
proof
  assume *: "p dvd x \<and> is_square (x div p)"
  have [simp]: "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "x = y ^ 2 * p"
    by (metis dvd_div_mult_self is_nth_powerE)
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
    
end