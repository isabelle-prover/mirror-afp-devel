header{*Perfect Number Theorem*}

theory Perfect
imports Sigma
begin

definition  perfect :: "nat => bool" where
"perfect m == m>0 & 2*m = sigma m"

theorem perfect_number_theorem:
  assumes even: "even m" and perfect: "perfect m"
  shows "\<exists> n . m = 2^n*(2^(n+1) - 1) \<and> prime (2^(n+1) - 1)"
proof
  from perfect have m0: "m>0" by (auto simp add: perfect_def)

  let ?n = "exponent 2 m" 
  let ?A = "m div 2^?n"
  let ?np = "(2::nat)^(?n+1) - 1"

  from even have "2 dvd m" by (simp add: nat_even_iff_2_dvd) 
  with m0 have n1: "?n >= 1 " by (simp add: exponent_ge two_is_prime)

  from m0 have  "2^?n dvd m" by (rule power_exponent_dvd)
  hence "m = 2^?n*?A" by (simp only: dvd_mult_div_cancel) 
  with m0 have mdef: "m=2^?n*?A & coprime 2 ?A"
    by (simp add: two_is_prime coprime_exponent)
  moreover with m0 have a0: "?A>0" by (metis nat_0_less_mult_iff)
  moreover
  { from perfect have "2*m=sigma(m)" by (simp add: perfect_def)
    with mdef have "2^(?n+1)*?A=sigma(2^?n*?A)" by auto
  } ultimately have "2^(?n+1)*?A=sigma(2^?n)*sigma(?A)"
    by (simp add: sigma_semimultiplicative two_is_prime)
  hence formula: "2^(?n+1)*?A=(?np)*sigma(?A)"
    by (simp only: sigma_prime_power_two)

  from n1 have "(2::nat)^(?n+1) >= 2^2" by (simp only: power_increasing)
  hence nplarger: "?np>= 3" by auto

  let ?B = "?A div ?np"

  from formula have "?np dvd 2^(?n+1)*?A" by auto
  hence             "?np dvd ?A"
    by (metis Suc_eq_plus1_left Suc_pred' add_is_0 coprime_divprod coprime_minus1 two_is_prime zero_less_prime_power zero_neq_one)
  hence bdef:       "?np*?B = ?A" by (simp add: dvd_mult_div_cancel)
  with a0 have  b0: "?B>0" by (metis gr0I mult_is_0)

  from nplarger a0 have bsmallera: "?B < ?A" by auto

  have "?B = 1"
  proof (rule ccontr)
    assume "~?B = 1"
    with b0 bsmallera have "1<?B" "?B<?A" by auto
    moreover from bdef have "?B : divisors ?A" by (rule mult_divisors2)
    ultimately have "1+?B+?A <= sigma ?A" by (rule sigma_third_divisor)
    with nplarger have "?np*(1+?A+?B) <= ?np*(sigma ?A)"
      by (auto simp only: nat_mult_le_cancel1)
    with bdef have "?np+?A*?np + ?A*1 <= ?np*(sigma ?A)"
      by (simp only: add_mult_distrib_three mult_commute)
    hence "?np+?A*(?np + 1) <= ?np*(sigma ?A)" by (simp only:add_mult_distrib2)
    with nplarger have "2^(?n+1)*?A < ?np*(sigma ?A)" by(simp add:mult_commute)
    with formula show "False" by auto
  qed

  with bdef have adef: "?A=?np" by auto
  with formula have "?np*2^(?n+1) =(?np)*sigma(?A)" by auto
  with nplarger adef have "?A + 1=sigma(?A)" by auto
  with a0 have "prime ?A" by (simp add: sigma_imp_prime)
  with mdef adef show "m = 2^?n*(?np) & prime ?np" by simp
qed

theorem Euclid_book9_prop36:
  assumes p: "prime (2^(n+1) - (1::nat))"
  shows "perfect ((2^n)*(2^(n+1) - 1))"
proof (unfold perfect_def, auto)
  from assms show "(2::nat)*2^n > Suc 0" by (auto simp add: prime_def)
next
  have p2: "prime 2" by (rule two_is_prime)
  moreover from p have "prime (2^(n+1) - 1)" by simp
  moreover have "2 ~= ((2::nat)^(n+1) - 1)" by simp arith
  ultimately have "coprime 2 (2^(n+1) - 1)" by (rule distinct_prime_coprime)
  with p p2 have "prime 2" "coprime 2 (2^(n+1) - 1)" "2^(n+1) - 1 > (0::nat)"
    by (auto simp add: prime_def)
  hence  "sigma (2^n*(2^(n+1) - 1)) = (sigma(2^n))*(sigma(2^(n+1) - 1))"
    by (simp only: sigma_semimultiplicative)
  also from assms have "... = (sigma(2^(n)))*(2^(n+1))"
    by (auto simp add: prime_imp_sigma)
  also have "... = (2^(n+1) - 1)*(2^(n+1))" by(simp add: sigma_prime_power_two)
  finally show "2*(2^n * (2*2^n - Suc 0)) = sigma(2^n*(2*2^n - Suc 0))" by auto
qed

end