(*  Title:  HyperLog.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>The hyper logarithm\<close>

theory HyperLog
  imports "Real_Power.Log" "HOL-Nonstandard_Analysis.NatStar" HyperrealPower
begin 


definition
  hLog :: "[hypreal,hypreal] => hypreal" where
  [transfer_unfold]: "hLog a x = starfun2 Log a x"

lemma hLog:
     "hLog (star_n X) (star_n Y) =  star_n (\<lambda>n. Log (X n) (Y n))"
by (metis hLog_def starfun2_star_n)

lemma hpow_hLog_cancel [simp]:
   "\<And>a x. \<lbrakk> a > 0; a \<noteq> 1; x > 0 \<rbrakk> \<Longrightarrow> a hpow (hLog a x) = x"
by transfer simp

lemma hLog_hpow_cancel [simp]: 
  "\<And>a y. \<lbrakk> 0 < a; a \<noteq> 1 \<rbrakk> \<Longrightarrow> hLog a (a hpow y) = y"
by transfer simp

lemma hLog_mult: 
  "\<And>a x y. \<lbrakk> 0 < a; a \<noteq> 1; 0 < x; 0 < y \<rbrakk> \<Longrightarrow> hLog a (x * y) = hLog a x + hLog a y"
by (transfer, rule Log_mult)

lemma hLog_one [simp]: 
  "\<And>a. \<lbrakk> 0 < a; a \<noteq> 1 \<rbrakk> \<Longrightarrow> hLog a 1 = 0"
by transfer simp

lemma hLog_eq_one [simp]: 
  "\<And>a. \<lbrakk> 0 < a; a \<noteq> 1 \<rbrakk> \<Longrightarrow> hLog a a = 1"
by transfer simp

lemma hLog_inverse:
  "\<And>a x. \<lbrakk> a > 0; a \<noteq> 1; x > 0 \<rbrakk> \<Longrightarrow> hLog a (inverse x) = - hLog a x"
by (transfer, rule Log_inverse)

lemma hLog_divide: 
  "\<And>a x y. \<lbrakk> 0 < a; a \<noteq> 1; 0 < x; 0 < y \<rbrakk> \<Longrightarrow> hLog a (x/y) = hLog a x - hLog a y"
by (transfer, rule Log_divide)

lemma hLog_less_cancel_iff [simp]:
     "\<And>a x y. \<lbrakk> 1 < a; 0 < x; 0 < y \<rbrakk> \<Longrightarrow> (hLog a x < hLog a y) = (x < y)"
by transfer simp

lemma hLog_inj: assumes "1 < b" shows "inj_on (hLog b) {0 <..}"
proof (rule inj_onI, simp)
  fix x y assume pos: "0 < x" "0 < y" and *: "hLog b x = hLog b y"
  show "x = y"
  proof (cases rule: linorder_cases)
    assume "x < y" hence "hLog b x < hLog b y"
      using hLog_less_cancel_iff[OF `1 < b`] pos by simp
    thus ?thesis using * by simp
  next
    assume "y < x" hence "hLog b y < hLog b x"
      using hLog_less_cancel_iff[OF `1 < b`] pos by simp
    thus ?thesis using * by simp
  qed simp
qed

lemma hLog_le_cancel_iff [simp]:
     "\<And>a x y. \<lbrakk> 1 < a; 0 < x; 0 < y \<rbrakk> \<Longrightarrow> (hLog a x \<le> hLog a y) = (x \<le> y)"
by transfer simp

lemma zero_less_hLog_cancel_iff [simp]: 
  "\<And>a x. 1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < hLog a x \<longleftrightarrow> 1 < x"
by transfer simp

lemma zero_le_hLog_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 \<le> hLog a x \<longleftrightarrow> 1 \<le> x"
  using hLog_le_cancel_iff[of a 1 x] by simp

lemma hLog_less_zero_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x\<Longrightarrow> hLog a x < 0 \<longleftrightarrow> x < 1"
  using hLog_less_cancel_iff[of a x 1] by simp

lemma hLog_le_zero_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> hLog a x \<le> 0 \<longleftrightarrow> x \<le> 1"
  using hLog_le_cancel_iff[of a x 1] by simp

lemma one_less_hLog_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x ==> 1 < hLog a x \<longleftrightarrow> a < x"
  using hLog_less_cancel_iff[of a a x] by simp

lemma one_le_hLog_cancel_iff[simp]: "1 < a ==> 0 < x \<Longrightarrow> 1 \<le> hLog a x \<longleftrightarrow> a \<le> x"
  using hLog_le_cancel_iff[of a a x] by simp

lemma hLog_less_one_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> hLog a x < 1 \<longleftrightarrow> x < a"
  using hLog_less_cancel_iff[of a x a] by simp

lemma hLog_le_one_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> hLog a x \<le> 1 \<longleftrightarrow> x \<le> a"
  using hLog_le_cancel_iff[of a x a] by simp

lemma hLog_hpow: "\<And>b x y. \<lbrakk> 0 < x; 1 < b; b \<noteq> 1 \<rbrakk> \<Longrightarrow> hLog b (x hpow y) = y * hLog b x"
by (transfer, rule Log_powreal)

lemma hLog_nat_power: 
      "\<And>b x n. \<lbrakk> 0 < x; 1 < b; b \<noteq> 1 \<rbrakk> \<Longrightarrow> hLog b (x pow n) = of_hypnat n * hLog b x"
by (transfer, simp add: Log_nat_power )

end