(*  Title:      RealPower/RatPower.thy
    Authors:    Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)

theory RatPower
imports HOL.NthRoot
begin

section \<open>Rational Exponents\<close>

text\<open>A few lemmas about nth-root.\<close>

lemma real_root_mult_exp_cancel:
  "\<lbrakk> 0 < x; 0 < m; 0 < n \<rbrakk> 
   \<Longrightarrow> root (m * n) (x ^ (k * n)) = root m (x ^ k)"
  by (simp add: power_mult real_root_pos_unique) 

lemma real_root_mult_exp_cancel1:
  "\<lbrakk> 0 < x; 0 < n \<rbrakk> \<Longrightarrow> root n (x ^ (k * n)) = x ^ k"
by (auto dest: real_root_mult_exp_cancel [of _ 1])

lemma real_root_mult_exp_cancel2:
  "\<lbrakk> 0 < x; 0 < m; 0 < n \<rbrakk> 
   \<Longrightarrow> root (n * m) (x ^ (n * k)) = root m (x ^ k)"
by (simp add: mult.commute real_root_mult_exp_cancel) 

lemma real_root_mult_exp_cancel3:
  "\<lbrakk> 0 < x; 0 < n \<rbrakk> \<Longrightarrow> root n (x ^ (n * k)) = x ^ k" 
by (auto dest: real_root_mult_exp_cancel2 [of _ 1])

text\<open>Definition of rational exponents,\<close>

definition
  powrat  :: "[real,rat] => real"     (infixr "pow\<^sub>\<rat>" 80) where
  "x pow\<^sub>\<rat> r = (if r > 0 
               then root (nat (snd(quotient_of r))) 
                          (x ^ (nat (fst(quotient_of r))))
               else root (nat (snd(quotient_of r))) 
                          (1/x ^ (nat (- fst(quotient_of r)))))"

(* Why isn't this a default simp rule?  *)
declare quotient_of_denom_pos' [simp]

lemma powrat_one_eq_one [simp]: "1 pow\<^sub>\<rat> a = 1"
  by (simp add: powrat_def)

lemma powrat_zero_eq_one [simp]: "x pow\<^sub>\<rat> 0 = 1"
by (simp add: powrat_def)

lemma powrat_one [simp]: "x pow\<^sub>\<rat> 1 = x"
by (simp add: powrat_def)

lemma powrat_mult_base: 
      "(x * y) pow\<^sub>\<rat> r = (x pow\<^sub>\<rat> r) * (y pow\<^sub>\<rat> r)"
proof (cases r)
  case (Fract a b)
  then show ?thesis 
    using powrat_def quotient_of_Fract real_root_mult [symmetric] 
          power_mult_distrib by fastforce
qed

lemma powrat_divide:
     "(x / y) pow\<^sub>\<rat> r = (x pow\<^sub>\<rat> r)/(y pow\<^sub>\<rat> r)"
proof (cases r)
  case (Fract a b)
  then show ?thesis 
    using powrat_def quotient_of_Fract real_root_divide [symmetric] 
          power_divide by fastforce
qed

lemma powrat_zero_base [simp]: 
  assumes "r \<noteq> 0" shows "0 pow\<^sub>\<rat> r = 0"
proof (cases r)
  case (Fract a b)
  then show ?thesis
  proof (cases "a > 0")
    case True
    then show ?thesis 
      using Fract powrat_def quotient_of_Fract zero_less_Fract_iff 
      by simp
  next
    case False
    then  have "a \<noteq> 0"
    using Fract(1) assms rat_number_collapse(1) by blast 
  then 
    show ?thesis
      using Fract powrat_def quotient_of_Fract zero_less_Fract_iff 
      by auto
  qed
qed


(* That's the one we want *)
lemma powrat_inverse:
      "(inverse y) pow\<^sub>\<rat> r = inverse(y pow\<^sub>\<rat> r)"
proof (cases "r=0")
  case True 
  then show ?thesis by simp
next
  case False
  then show ?thesis
    by (simp add: inverse_eq_divide powrat_divide)  
qed

lemma powrat_minus:
   "x pow\<^sub>\<rat> (-r) = inverse (x pow\<^sub>\<rat> r)"
proof (cases r)
  case (Fract a b)
  then show ?thesis 
    by (auto simp add: powrat_def divide_inverse real_root_inverse 
                       quotient_of_Fract zero_less_Fract_iff)
qed

lemma powrat_gt_zero: 
  assumes "x > 0" shows "x pow\<^sub>\<rat> r > 0"
proof (cases r)
  case (Fract a b)
  then show ?thesis
    by (simp add: assms powrat_def) 
qed

lemma powrat_not_zero: 
  assumes "x \<noteq> 0" shows "x pow\<^sub>\<rat> r \<noteq> 0"
proof (cases r)
  case (Fract a b)
  then show ?thesis
    by (simp add: assms powrat_def) 
qed

(* Not in GCD.thy *)
lemma gcd_add_mult_commute: "gcd (m::'a::semiring_gcd) (n + k * m) = gcd m n"
  by (metis add.commute gcd_add_mult)

lemma coprime_add_mult_iff1 [simp]: 
     "coprime (n + k * m) (m::'a::semiring_gcd) = coprime n m"
  by (simp add: coprime_iff_gcd_eq_1 gcd.commute gcd_add_mult_commute)

lemma coprime_add_mult_iff2 [simp]: 
     "coprime (k * m + n) (m::'a::semiring_gcd) = coprime n m"
  by (simp add: add.commute)

(* Not proved before?? *)
lemma gcd_mult_div_cancel_left1 [simp]: 
  "gcd a b * (a div gcd a b)  = (a::'a::semiring_gcd)"
  by simp

lemma gcd_mult_div_cancel_left2 [simp]: 
  "gcd b a * (a div gcd b a)  = (a::'a::semiring_gcd)"
  by simp

lemma gcd_mult_div_cancel_right1 [simp]: 
  "(a div gcd a b) * gcd a b  = (a::'a::semiring_gcd)"
  by simp

lemma gcd_mult_div_cancel_right2 [simp]:
  "(a div gcd b a) * gcd b a = (a::'a::semiring_gcd)"
  by simp
(* END: Not in GCD.thy *)

lemma real_root_normalize_cancel:
  assumes "0 < x" and "a \<noteq> 0" and "b > 0"
  shows "root (nat(snd(Rat.normalize(a,b)))) 
               (x ^ nat(fst(Rat.normalize(a,b)))) = 
         root (nat b) (x ^ (nat a))"
proof -
  have "root (nat (b div gcd a b)) (x ^ nat (a div gcd a b)) = 
        root (nat b) (x ^ nat a)"
  proof (cases "coprime a b")
    case True
      then show ?thesis by simp
  next
    case False
      have "0 < gcd a b"
        using assms(2) gcd_pos_int by blast
      then have "nat (gcd a b) > 0"
        by linarith 
      moreover have "nat (b div gcd a b) > 0" 
        using nonneg1_imp_zdiv_pos_iff assms(3) by auto
      moreover
       have "root (nat b) (x ^ nat a) = 
             root (nat (gcd a b * (b div gcd a b))) 
                   (x ^ nat (gcd a b * (a div gcd a b)))"
         by simp 
       ultimately show ?thesis
         using assms(1) gcd_ge_0_int nat_mult_distrib real_root_mult_exp_cancel2 
         by presburger
     qed
     then show ?thesis
       by (metis assms(3) fst_conv normalize_def snd_conv) 
  qed

lemma powrat_add_pos: 
  assumes "0 < x" and "0 < r" and "0 < s" 
  shows "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
proof (cases r)
  case (Fract a b)
  assume b0: "b > 0" and rf: "r = Fract a b"
  then have a0: "a > 0"
    using Fract(1) assms(2) zero_less_Fract_iff by blast 
  then show ?thesis
    proof (cases s)
      case (Fract c d) 
      assume d0: "d > 0" and sf: "s = Fract c d" 
      then have c0: "c > 0"
        using assms(3) zero_less_Fract_iff by blast 
      then have bd0: "b * d > 0"  
          using b0 zero_less_mult_iff Fract(2) by blast 
          then show ?thesis 
          proof (cases "a * d > 0 \<and> c * b > 0")
            case True
            assume abcd: "a * d > 0 \<and> c * b > 0"
            then have adcb0: "a * d + c * b > 0" by simp
            have "x ^ nat (a * d + c * b) = 
                  ((x ^ (nat a)) ^ nat d) * (x ^ (nat c)) ^ nat b"
              using abcd nat_mult_distrib nat_add_distrib 
                    zero_less_Fract_iff Fract(3) a0 c0 
              by (simp add: power_mult power_add)
            then have "root (nat b) 
                        (root (nat d) 
                           (x ^ nat (a * d + c * b))) =
                       root (nat b) 
                        (root (nat d) 
                          (((x ^ (nat a)) ^ nat d) * (x ^ (nat c)) ^ nat b))"
              by simp   
            also have "... = root (nat b) 
                              (root (nat d) ((x ^ (nat a)) ^ nat d) * 
                               root (nat d) ((x ^ (nat c)) ^ nat b))"
              by (simp add: Fract(2) real_root_mult)
            also have "... = root (nat b) 
                              (root (nat d) ((x ^ (nat a)) ^ nat d)) *
                             root (nat b) 
                              (root (nat d) ((x ^ (nat c)) ^ nat b))"
              using real_root_mult by blast
            also have "... = root (nat b) (x ^ (nat a)) * 
                             root (nat b) 
                              (root (nat d) ((x ^ (nat c)) ^ nat b))"
              using real_root_power_cancel Fract(2) zero_less_nat_eq assms(1) 
                    less_imp_le by simp
            also have "... = 
                       root (nat b) (x ^ nat a) *  root (nat d) (x ^ nat c)"
              using  real_root_power [of "nat d"] real_root_power_cancel 
                     real_root_pos_pos_le zero_less_nat_eq
                     Fract(2) zero_less_nat_eq b0 assms(1) by auto 
            finally have "root (nat b) (root (nat d) (x ^ nat (a * d + c * b))) = 
                          root (nat b) (x ^ nat a) *  root (nat d) (x ^ nat c)" 
              by assumption        
            then show ?thesis using a0 b0 c0 d0 bd0 abcd adcb0 assms(1) sf rf 
              by (auto simp add:  powrat_def quotient_of_Fract 
                      real_root_mult_exp nat_mult_distrib 
                      zero_less_Fract_iff real_root_normalize_cancel)
          next
            case False
            then show ?thesis
              by (simp add: a0 b0 c0 d0) 
          qed
    qed
qed

lemma powrat_add_neg: 
  assumes "0 < x" and "r < 0" and "s < 0" 
  shows "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
proof - 
  have "x pow\<^sub>\<rat> (- r + - s) = x pow\<^sub>\<rat> - r * x pow\<^sub>\<rat> - s" 
    using assms powrat_add_pos neg_0_less_iff_less by blast 
  then show ?thesis
    by (metis inverse_eq_imp_eq inverse_mult_distrib 
         minus_add_distrib powrat_minus) 
qed

lemma powrat_add_neg_pos: 
    assumes pos_x: "0 < x" and  
            neg_r: "r < 0" and 
            pos_s: "0 < s" 
    shows "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
proof (cases "r + s > 0")
  assume exp_pos: "r + s > 0"
  have "-r > 0" using neg_r by simp 
  then have "x pow\<^sub>\<rat> (r + s) * (x pow\<^sub>\<rat> -r) =  (x pow\<^sub>\<rat> s)" 
    using exp_pos pos_x powrat_add_pos by fastforce 
  then have "x pow\<^sub>\<rat> (r + s) * inverse (x pow\<^sub>\<rat> r) =  (x pow\<^sub>\<rat> s)" 
    by (simp add: powrat_minus) 
  then show "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
    by (metis Groups.mult_ac(3) assms(1) mult.right_neutral 
          order_less_irrefl powrat_gt_zero right_inverse)  
next
  assume exp_pos: "\<not> r + s > 0"   
  then have "r + s = 0 \<or> r + s < 0" using neq_iff by blast   
  then show "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)" 
  proof 
    assume exp_zero: "r + s = 0" 
    then have "x pow\<^sub>\<rat> (r + s) = 1" by simp
    also have "... = (x pow\<^sub>\<rat> r) * inverse (x pow\<^sub>\<rat> r)" 
      using pos_x powrat_not_zero by simp
    also have "... = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> - r)" 
      by (simp add: powrat_minus) 
    finally show "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"  
      using exp_zero minus_unique by blast 
   next 
    assume "r + s < 0" 
    have "-s < 0" using pos_s by simp 
    then have "x pow\<^sub>\<rat> (r + s) * (x pow\<^sub>\<rat> -s) =  (x pow\<^sub>\<rat> r)" 
      using \<open>r + s < 0\<close> pos_x powrat_add_neg by fastforce 
    then have "x pow\<^sub>\<rat> (r + s) * inverse (x pow\<^sub>\<rat> s) =  (x pow\<^sub>\<rat> r)" 
      by (simp add: powrat_minus) 
    then show "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
      by (metis divide_eq_eq divide_real_def 
            less_irrefl pos_x powrat_not_zero) 
    qed
qed

lemma powrat_add_pos_neg: 
 "\<lbrakk> 0 < x; 0 < r; s < 0 \<rbrakk> 
  \<Longrightarrow> x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
by (metis add.commute mult.commute powrat_add_neg_pos)

lemma powrat_add: 
  assumes "0 < x" 
  shows "x pow\<^sub>\<rat> (r + s) = (x pow\<^sub>\<rat> r) * (x pow\<^sub>\<rat> s)"
  proof (cases "(r > 0 \<or> r \<le> 0) \<and> (s > 0 \<or> s \<le> 0)")
    case True
    then show ?thesis using assms 
      by (auto dest: powrat_add_pos powrat_add_neg powrat_add_neg_pos 
           powrat_add_pos_neg simp add: le_less)
next
  case False
  then show ?thesis  by auto
qed

lemma powrat_diff: 
     "0 < x \<Longrightarrow>  x pow\<^sub>\<rat> (a - b) = x pow\<^sub>\<rat> a / x pow\<^sub>\<rat> b"
by (metis add_uminus_conv_diff divide_inverse powrat_add powrat_minus)

lemma powrat_mult_pos:
  assumes "0 < x" and "0 < r" and "0 < s" 
  shows "x pow\<^sub>\<rat> (r * s) = (x pow\<^sub>\<rat> r) pow\<^sub>\<rat> s" 
proof (cases r)
  case (Fract a b)
  assume b0: "b > 0" and rf: "r = Fract a b" and coab: "coprime a b"
  have a0: "a > 0"
    using assms(2) b0 rf zero_less_Fract_iff by blast 
  then show ?thesis 
  proof (cases s)
    case (Fract c d)
    assume d0: "d > 0" and sf: "s = Fract c d" and coad: "coprime c d"
      then have c0: "c > 0"
        using assms(3) zero_less_Fract_iff by blast 
      then have  "b * d > 0" 
        using b0 d0 by simp
      then show ?thesis using a0 c0 b0 d0 rf sf coab coad assms
        by (auto intro: mult_pos_pos simp add: powrat_def quotient_of_Fract
            zero_less_Fract_iff real_root_normalize_cancel real_root_power
            real_root_mult_exp [symmetric] nat_mult_distrib power_mult 
            mult.commute)
  qed
qed

lemma powrat_mult_neg:
  assumes "0 < x" "r < 0" and "s < 0" 
  shows "x pow\<^sub>\<rat> (r * s) = (x pow\<^sub>\<rat> r) pow\<^sub>\<rat> s"
proof - 
  have " x pow\<^sub>\<rat> (- r * - s) = (x pow\<^sub>\<rat> - r) pow\<^sub>\<rat> - s" 
    using powrat_mult_pos assms neg_0_less_iff_less by blast 
  then show ?thesis
    by (simp add: powrat_inverse powrat_minus) 
qed 


lemma powrat_mult_neg_pos:
  assumes "0 < x" and "r < 0" and "0 < s" 
  shows "x pow\<^sub>\<rat> (r * s) = (x pow\<^sub>\<rat> r) pow\<^sub>\<rat> s"
proof -
  have "x pow\<^sub>\<rat> (- r * s) = (x pow\<^sub>\<rat> - r) pow\<^sub>\<rat> s" 
    using powrat_mult_pos assms neg_0_less_iff_less by blast 
  then show ?thesis
    by (simp add: powrat_inverse powrat_minus) 
qed

lemma powrat_mult_pos_neg:
  assumes "0 < x" and "0 < r" and "s < 0"
  shows "x pow\<^sub>\<rat> (r * s) = (x pow\<^sub>\<rat> r) pow\<^sub>\<rat> s"
proof -
  have "x pow\<^sub>\<rat> (r * - s) = (x pow\<^sub>\<rat> r) pow\<^sub>\<rat> - s" 
    using powrat_mult_pos assms neg_0_less_iff_less by blast 
  then show ?thesis
    by (simp add: powrat_minus) 
qed

lemma powrat_mult:
  assumes "0 < x" shows "x pow\<^sub>\<rat> (r * s) = (x pow\<^sub>\<rat> r) pow\<^sub>\<rat> s"
proof -
  {fix q::rat
    assume "q = 0" then have "x pow\<^sub>\<rat> (q * s) = (x pow\<^sub>\<rat> q) pow\<^sub>\<rat> s"
      by simp
  }
  then show ?thesis
    by (metis assms linorder_neqE_linordered_idom mult_zero_right 
         powrat_mult_neg powrat_mult_neg_pos powrat_mult_pos 
         powrat_mult_pos_neg powrat_zero_eq_one)
qed

lemma powrat_less_mono: 
  assumes "r < s" and "1 < x" 
  shows "x  pow\<^sub>\<rat> r < x pow\<^sub>\<rat> s"
  proof (cases r)
    case (Fract a b)
    assume r_assms: "r = Fract a b" "0 < b" "coprime a b"
    then show ?thesis
  proof (cases s)
    case (Fract c d)
    assume s_assms: "s = Fract c d" "0 < d" "coprime c d"
    have adcb: "a * d < c * b" 
      using assms r_assms s_assms by auto
    have b_ba: "0 < nat (b * d)"
      by (simp add: r_assms(2) s_assms(2))
    have root0: "0 \<le> root (nat d) (x ^ nat c)" 
                "0 \<le> root (nat d) (1 / x ^ nat (- c))"
      using assms(2) real_root_pos_pos_le by auto 
    then show ?thesis
    proof (auto simp add: powrat_def quotient_of_Fract zero_less_Fract_iff 
                          s_assms r_assms)
      assume ac0: "0 < a" "0 < c"
      then have "(x ^ nat a) ^ nat d < (x ^ nat c) ^ nat b"
        using adcb assms(2) r_assms(2) less_imp_le mult_pos_pos 
              nat_mono_iff nat_mult_distrib power_mult 
              power_strict_increasing 
        by metis
      then have "root (nat b) (x ^ nat a) ^ nat (b * d) <
                  root (nat d) (x ^ nat c) ^ nat (b * d)" 
        using assms r_assms s_assms ac0 real_root_power 
              [symmetric] nat_mult_distrib
        by (auto simp add:  power_mult)
      then show "root (nat b) (x ^ nat a) < root (nat d) (x ^ nat c)"
        using power_less_imp_less_base root0(1) by blast
    next
      assume "0 < a" "\<not> 0 < c"
      then show "root (nat b) (x ^ nat a) < 
                  root (nat d) (1 / x ^ nat (- c))"
        using assms(1) less_trans r_assms(1) r_assms(2) s_assms(1) 
              s_assms(2) zero_less_Fract_iff by blast
    next 
      assume ac0: "\<not> 0 < a" "0 < c"
      then have "a = 0 \<or> a < 0" by auto
      then show "root (nat b) (1 / x ^ nat (- a)) <
                  root (nat d) (x ^ nat c)"
      proof 
        assume "a = 0" then show ?thesis
          by (simp add: ac0(2) assms(2) r_assms(2) s_assms(2))
      next
        assume a0: "a < 0"  
        have "(1 / x ^ nat (- a)) ^ nat d < 1" 
          using a0 s_assms(2) assms(2) adcb power_mult [symmetric] 
                power_one_over nat_mult_distrib [symmetric]
          by (metis (no_types) eq_divide_eq_1 inverse_eq_divide inverse_le_1_iff
              le_less neg_0_less_iff_less one_less_power power_one_over
              zero_less_nat_eq)
        moreover have "1 < (x ^ nat c) ^ nat b"
          by (simp add: ac0(2) assms(2) r_assms(2)) 
        ultimately have "(1 / x ^ nat (- a)) ^ nat d < (x ^ nat c) ^ nat b"
          by linarith 
        then have "root (nat b) (1 / x ^ nat (- a)) ^ nat (b * d)
                    < root (nat d) (x ^ nat c) ^ nat (b * d)"
        using  assms r_assms s_assms ac0 real_root_power [symmetric] nat_mult_distrib
        by (auto simp add:  power_mult)
        then show ?thesis
          using power_less_imp_less_base root0(1) by blast 
      qed
    next
      assume ac0: "\<not> 0 < a" "\<not> 0 < c"   
      then show "root (nat b) (1 / x ^ nat (- a)) < 
                  root (nat d) (1 / x ^ nat (- c))"
      proof (cases "a = 0 \<or> c = 0")
        assume "a = 0 \<or> c = 0" then show ?thesis
          using assms r_assms s_assms adcb ac0  
          by (auto simp add: not_less le_less)
      next
        assume "\<not> (a = 0 \<or> c = 0)" 
        then have ac00: "a < 0" "c < 0" using ac0 by auto
        then have "1 / x ^ nat (- (a * d)) < 
                    1 / x ^ nat (- (c * b))" 
          using ac00 r_assms s_assms assms 
          by (simp add: divide_inverse mult_pos_neg2) 
        then have "(1 / x ^ nat (- a)) ^ nat d < 
                    (1 / x ^ nat (- c)) ^ nat b" 
          using s_assms r_assms  ac00
          by (auto simp add: power_mult [symmetric] 
                power_one_over nat_mult_distrib [symmetric])
        then have "root (nat b) (1 / x ^ nat (- a)) ^ nat (b * d)
                   < root (nat d) (1 / x ^ nat (- c)) ^ nat (b * d)"
          using assms r_assms s_assms ac0 real_root_power [symmetric] 
                nat_mult_distrib
        by (auto simp add:  power_mult)
      then show "root (nat b) (1 / x ^ nat (- a)) < 
                  root (nat d) (1 / x ^ nat (- c))"
          using power_less_imp_less_base root0(2) by blast
      qed
    qed
  qed
qed

lemma power_le_imp_le_base2: 
  "\<lbrakk> (a::'a::linordered_semidom) ^ n \<le> b ^ n; 0 \<le> b; 0 < n \<rbrakk> 
   \<Longrightarrow> a \<le> b"
by (auto intro: power_le_imp_le_base [of _ "n - 1"])

lemma powrat_le_mono: 
  assumes "r \<le> s" and "1 \<le> x" 
  shows "x  pow\<^sub>\<rat> r \<le> x pow\<^sub>\<rat> s"
  by (metis (full_types) assms le_less powrat_less_mono powrat_one_eq_one)

lemma powrat_less_cancel: 
  "\<lbrakk> x  pow\<^sub>\<rat> r < x  pow\<^sub>\<rat> s; 1 < x \<rbrakk> \<Longrightarrow> r < s"
  by (metis not_less_iff_gr_or_eq powrat_less_mono)

(* Monotonically increasing *)
lemma powrat_less_cancel_iff [simp]: 
  "1 < x \<Longrightarrow> (x pow\<^sub>\<rat> r < x pow\<^sub>\<rat> s) = (r < s)"
by (blast intro: powrat_less_cancel powrat_less_mono)

lemma powrat_le_cancel_iff [simp]: 
  "1 < x \<Longrightarrow> (x  pow\<^sub>\<rat> r \<le> x  pow\<^sub>\<rat> s) = (r \<le> s)"
by (simp add: linorder_not_less [symmetric])

(* Next 2 theorems should be in Power.thy *)
lemma power_inject_exp_less_one [simp]:
  "\<lbrakk>0 < a; (a::'a::{linordered_field}) < 1 \<rbrakk> 
   \<Longrightarrow> a ^ m = a ^ n \<longleftrightarrow> m = n"
by (metis less_irrefl nat_neq_iff power_strict_decreasing)

lemma power_inject_exp_strong [simp]:
  "\<lbrakk>0 < a; (a::'a::{linordered_field}) \<noteq> 1 \<rbrakk> 
   \<Longrightarrow> a ^ m = a ^ n \<longleftrightarrow> m = n"
by (case_tac "a < 1") (auto simp add: not_less)

(* Not proved elsewhere? *)
lemma nat_eq_cancel: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> (nat a = nat b) = (a = b)"
by auto

lemma powrat_inject_exp [simp]: 
  "1 < x  \<Longrightarrow> (x pow\<^sub>\<rat> r = x pow\<^sub>\<rat> s) = (s = r)"
  by (metis neq_iff powrat_less_cancel_iff)

lemma powrat_inject_exp_less_one [simp]: 
  assumes "0 < x" and "x < 1" 
  shows "(x pow\<^sub>\<rat> r = x pow\<^sub>\<rat> s) = (s = r)"
proof -
  have "1 < inverse x"
    using assms one_less_inverse by blast 
  then show ?thesis
    using powrat_inject_exp powrat_inverse by fastforce 
qed

lemma powrat_inject_exp_strong [simp]:
   "\<lbrakk> 0 < x; x \<noteq> 1 \<rbrakk>  \<Longrightarrow> (x pow\<^sub>\<rat> r = x pow\<^sub>\<rat> s) = (s = r)"
  using powrat_inject_exp_less_one by fastforce

(* Monotonically decreasing *)
lemma powrat_less_1_cancel_iff [simp]: 
  assumes x0: "0 < x" and x1: "x < 1" 
  shows "(x pow\<^sub>\<rat> r < x pow\<^sub>\<rat> s) = (s < r)"
proof 
  assume xrs: "x pow\<^sub>\<rat> r < x pow\<^sub>\<rat> s" 
  have invx: "1 < 1/x" using assms by simp
  have  "r < s \<or> r \<ge> s" using leI by blast 
  then show "s < r" 
  proof
    assume "r < s"
    then have " inverse x pow\<^sub>\<rat> r < inverse x pow\<^sub>\<rat> s" using invx
      by (simp add: inverse_eq_divide)
    then have " x pow\<^sub>\<rat> s < x pow\<^sub>\<rat> r"
      by (simp add: powrat_gt_zero powrat_inverse x0) 
    then show ?thesis using xrs by linarith 
  next
    assume "r \<ge> s"   
    then show ?thesis
      using less_eq_rat_def xrs by blast 
  qed
next 
  assume sr: "s < r" 
  have invx: "1 < 1/x" using assms by simp
  then have " inverse x pow\<^sub>\<rat> s < inverse x pow\<^sub>\<rat> r" using invx sr
    by (simp add: inverse_eq_divide) 
  then  show "x pow\<^sub>\<rat> r < x pow\<^sub>\<rat> s"
    by (simp add: powrat_gt_zero powrat_inverse x0)
qed
 
lemma powrat_le_1_cancel_iff [simp]: 
   "\<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> (x pow\<^sub>\<rat> r \<le> x pow\<^sub>\<rat> s) = (s \<le> r)"
by (auto simp add: le_less)

lemma powrat_ge_one: "x \<ge> 1 \<Longrightarrow> r \<ge> 0 \<Longrightarrow> x pow\<^sub>\<rat> r \<ge> 1"
by (metis powrat_le_mono powrat_zero_eq_one)

lemma isCont_powrat:
  assumes "0 < x" shows "isCont (\<lambda>x. x pow\<^sub>\<rat> r) x"
proof (cases r)
  case (Fract a b)
    assume fract_assms: "r = Fract a b" "0 < b" "coprime a b"
    then show ?thesis
    proof (cases "0 < a")
      case True
      then show ?thesis 
        using fract_assms isCont_o2 [OF isCont_power [OF continuous_ident]]
        by (auto intro: isCont_real_root simp add: powrat_def zero_less_Fract_iff)
      next
        case False
        then show ?thesis 
          using fract_assms assms isCont_real_root  real_root_gt_zero
                continuous_at_within_inverse [intro!]
          by (auto intro!: isCont_o2 [OF isCont_power [OF continuous_ident]]
                   simp add: powrat_def zero_less_Fract_iff divide_inverse 
                      real_root_inverse)
      qed
qed

lemma LIMSEQ_powrat_base: 
  "\<lbrakk> X \<longlonglongrightarrow> a; a > 0 \<rbrakk> \<Longrightarrow> (\<lambda>n. (X n) pow\<^sub>\<rat> q) \<longlonglongrightarrow> a pow\<^sub>\<rat> q"
by (metis isCont_tendsto_compose [where g="\<lambda>x. x pow\<^sub>\<rat> q"] isCont_powrat)

lemma powrat_inverse_of_nat_ge_one [simp]: 
      "a \<ge> 1 \<Longrightarrow> a pow\<^sub>\<rat> (inverse (of_nat n)) \<ge> 1"
  by (simp add: powrat_ge_one)

lemma powrat_inverse_of_nat_le_self [simp]: 
  assumes "1 \<le> a" shows "a pow\<^sub>\<rat> inverse (rat_of_nat n) \<le> a"
proof - 
  have "inverse (rat_of_nat n) \<le> 1"  
    by (auto simp add: inverse_le_1_iff)
  also have "a pow\<^sub>\<rat> 1 \<le> a" by simp
  ultimately show ?thesis
    using assms powrat_le_mono by fastforce 
qed

(* This lemma used to be in Limits.thy *)
lemma BseqI2': "\<forall>n\<ge>N. norm (X n) \<le> K \<Longrightarrow> Bseq X"
  using BfunI eventually_sequentially by blast

lemma Bseq_powrat_inverse_of_nat_ge_one:
      "a \<ge> 1 \<Longrightarrow> Bseq (\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n)))"
by (auto intro: BseqI2' [of 1 _ a] simp add: less_imp_le powrat_gt_zero)

lemma decseq_powrat_inverse_of_nat_ge_one:
      "a \<ge> 1 \<Longrightarrow> decseq (\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat (Suc n))))"
unfolding decseq_def by (auto intro: powrat_le_mono)

lemma convergent_powrat_inverse_Suc_of_nat_ge_one:
  assumes "a \<ge> 1" 
  shows "convergent (\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat (Suc n))))"
proof -
  have "Bseq (\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat n))" 
    using Bseq_powrat_inverse_of_nat_ge_one assms by blast
  then have "Bseq (\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat (Suc n)))"
    using Bseq_ignore_initial_segment [of _ 1] by fastforce 
  also have "monoseq (\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat (Suc n)))"
    using assms decseq_imp_monoseq decseq_powrat_inverse_of_nat_ge_one by blast
  ultimately show ?thesis
    using Bseq_monoseq_convergent by blast
qed

lemma convergent_powrat_inverse_of_nat_ge_one:
  assumes "a \<ge> 1" shows "convergent (\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n)))"
proof -
  have "convergent (\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat (Suc n)))"
    using convergent_powrat_inverse_Suc_of_nat_ge_one assms by blast
  then obtain L where "(\<lambda>n. a pow\<^sub>\<rat> inverse (1 + rat_of_nat n)) \<longlonglongrightarrow> L" 
    using convergent_def by auto
  then have "(\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat (n + 1))) \<longlonglongrightarrow> L" 
    by simp
  then have "(\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat n)) \<longlonglongrightarrow> L" 
    by (rule LIMSEQ_offset  [of _ 1])
  then show ?thesis using convergent_def by auto
qed

lemma LIMSEQ_powrat_inverse_of_nat_ge_one: 
  assumes "a \<ge> 1" shows "(\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow> 1"
proof -
  have "convergent(\<lambda>n. a pow\<^sub>\<rat> inverse (rat_of_nat n))"  
    using convergent_powrat_inverse_of_nat_ge_one assms by blast
  then have "\<exists>L. L \<noteq> 0 \<and> (\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow> L"
    using assms convergent_def powrat_inverse_of_nat_ge_one 
          LIMSEQ_le_const not_one_le_zero
    by metis 
  then obtain L 
       where l0: "L \<noteq> 0" 
       and liml: "(\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow> L" 
    by blast
  then have "(\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n)) * 
                   a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow> L * L"
    by (simp add:  tendsto_mult)
  then have "(\<lambda>n. a pow\<^sub>\<rat> (2 * inverse (of_nat n))) \<longlonglongrightarrow>  L * L"
    using powrat_add [symmetric] assms by simp
  also have "(2::nat) > 0" by simp
  ultimately 
  have "(\<lambda>n. a pow\<^sub>\<rat> (2 * inverse (of_nat (n * 2)))) \<longlonglongrightarrow>  L * L" 
    using LIMSEQ_linear [of _ "L * L" 2] by blast
  then have "(\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow>  L * L" 
    by simp
  then show ?thesis using liml using LIMSEQ_unique l0 
    by fastforce
qed

lemma LIMSEQ_powrat_inverse_of_nat_pos_less_one: 
  assumes a0: "0 < a" and a1: "a < 1" 
  shows "(\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow> 1"
proof - 
  have "inverse a > 1" using a0 a1
    using one_less_inverse by blast 
  then have "(\<lambda>n. inverse a pow\<^sub>\<rat> inverse (rat_of_nat n)) \<longlonglongrightarrow> 1"
    using LIMSEQ_powrat_inverse_of_nat_ge_one by simp 
  then have "(\<lambda>n. inverse (a pow\<^sub>\<rat> inverse (rat_of_nat n))) \<longlonglongrightarrow> 1"
    using powrat_inverse by simp
  then have "(\<lambda>x. 1 / inverse (a pow\<^sub>\<rat> inverse (rat_of_nat x))) \<longlonglongrightarrow> 1/1"
    by (auto intro: tendsto_divide simp only:)
  then show ?thesis  by (auto simp add: divide_inverse)
qed

lemma LIMSEQ_powrat_inverse_of_nat: 
   "a > 0 \<Longrightarrow> (\<lambda>n. a pow\<^sub>\<rat> (inverse (of_nat n))) \<longlonglongrightarrow> 1"
  by (metis LIMSEQ_powrat_inverse_of_nat_ge_one 
       LIMSEQ_powrat_inverse_of_nat_pos_less_one leI)


lemma real_root_eq_powrat_inverse:
  assumes "n > 0" shows "root n x = x pow\<^sub>\<rat> (inverse (of_nat n))"
proof (cases n)
  case 0
  then show ?thesis
    using assms by blast 
next
  case (Suc m)
  assume nSuc: "n = Suc m"
  then have "root (Suc m) x = root (nat (1 + int m)) x"
    by (metis nat_int of_nat_Suc)    
  then show ?thesis 
    by (auto simp add: nSuc powrat_def of_nat_rat 
          zero_less_Fract_iff quotient_of_Fract)
qed

lemma powrat_power_eq: 
   "0 < a \<Longrightarrow> a pow\<^sub>\<rat> rat_of_nat n = a ^ n"
proof (induction n)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case using powrat_add by simp
qed

end