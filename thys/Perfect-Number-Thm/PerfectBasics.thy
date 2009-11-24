header{*Basics needed*}

theory PerfectBasics
imports Main Divides Primes NatBin "~~/src/HOL/Algebra/Exponent"
begin

lemma setsum_mono4:
   assumes "finite (A::nat set)" and "finite (B::nat set)" and "A <= B"
   shows "\<Sum> A <= \<Sum> B"
by (auto simp add: setsum_mono2 assms)

lemma emptysetsumstozero: "A={} ==> \<Sum> (A::nat set) = 0" by simp
lemma smallerorequal: "(x::nat) <= Suc n <-> x <= n \<or> x = Suc n" by auto
lemma seteq_imp_setsumeq: "A=B ==> \<Sum> A = \<Sum> B" by auto

lemma exp_is_max_div:
   assumes m0:"m>0" and p: "prime p"
   shows "~ p dvd (m div (p^(exponent p m)))"
proof (rule ccontr)
 assume "~ ~ p dvd (m div (p^(exponent p m)))"
 hence a:"p dvd (m div (p^(exponent p m)))" by auto
 from m0 have "p^(exponent p m) dvd m" by (auto simp add: power_exponent_dvd)
 with a have "p*(p^exponent p m) dvd m" by (metis divides_mul_l dvd_mult_div_cancel local.a nat_mult_commute)
 with p have "m=0" by (auto simp add: power_Suc_exponent_Not_dvd)
 with m0 show "False" by auto
qed

lemma coprime_exponent:
  assumes p:"prime p" and m:"m>0"
  shows "coprime p (m div (p^(exponent p m)))"
proof (rule ccontr)
  assume " ~ coprime p (m div p ^ exponent p m)"
  hence "EX q. prime q & q dvd p & q dvd (m div (p^(exponent p m)))" by (auto simp add: coprime_prime_dvd_ex)
  hence "EX q. q = p & q dvd (m div (p^(exponent p m)))"
apply (metis p prime_1 prime_def) done
  hence  "EX q. p dvd (m div (p^(exponent p m)))" by auto
  hence "p dvd (m div (p^(exponent p m)))" by auto
  with p m show "False" by (auto simp add: exp_is_max_div)
qed

lemma add_mult_distrib_three: "(x::nat)*(a+b+c)=x*a+x*b+x*c" 
proof -
  have "(x::nat)*(a+b+c) = x*((a+b)+c)" by auto
  hence "x*(a+b+c) = x*(a+b)+x*c" by (metis add_mult_distrib2 nat_add_commute nat_add_left_commute)
  thus "x*(a+b+c) = x*a+x*b+x*c" by (metis add_mult_distrib2 nat_add_commute nat_add_left_commute) 
qed

lemma nat_interval_minus_zero: "{0..Suc n} = {0} Un {Suc 0..Suc n}" by auto
lemma nat_interval_minus_zero2:
 assumes "n>0"
 shows "{0..n} = {0} Un {Suc 0..n}" by (auto simp add: nat_interval_minus_zero)

lemma distribute_min_mult: "((a::nat) - 1)*c=a*c - c" by (metis diff_mult_distrib2 nat_mult_1_right nat_mult_commute)
theorem simplify_sum_of_powers: "(x - 1::nat) * (\<Sum>i=0 .. n . x^i)  = x^(n + 1) - 1" (is "?l = ?r")
proof (cases)
  assume "n = 0"
  thus "?l = x^(n+1) - 1" by auto
  next
  assume "n~=0"
  hence n0: "n>0" by auto 
  have "?l  = (x::nat)*(\<Sum>i=0 .. n . x^i) - (\<Sum>i=0 .. n . x^i)" by (simp only: distribute_min_mult)
  also have "... = (\<Sum>i=0 .. n . x^(Suc i))    - (\<Sum>i=0 .. n . x^i)" by (simp add: setsum_right_distrib)
  also have "... = (\<Sum>i=Suc 0 .. Suc n . x^i)  - (\<Sum>i=0 .. n . x^i)" by (metis One_nat_def setsum_shift_bounds_cl_Suc_ivl)
  also with n0 have "... = ((\<Sum>i=Suc 0 .. n . x^i)+x^(Suc n)) - (x^0 + (\<Sum>i=Suc 0 .. n . x^i))"  by (auto simp add: setsum_Un_disjoint nat_interval_minus_zero2)
  finally show "?thesis" by auto
qed

end