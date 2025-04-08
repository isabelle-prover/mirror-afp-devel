theory Theta_Functions_Library
imports
  "HOL-Computational_Algebra.Computational_Algebra"
begin
            
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