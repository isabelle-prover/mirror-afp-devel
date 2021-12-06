(*  Title:      RealPower/Log.thy
    Authors:    Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)  

section\<open>Real Logarithms (Redefined)\<close>

theory Log
imports RealPower
begin

text\<open>We can now directly define real logarithm of @{term x} to base @{term a}.\<close>

definition
    Log  :: "[real,real] \<Rightarrow> real" where
   "Log a x = (THE y. a pow\<^sub>\<real> y = x)"

lemma IVT_simple: 
  "\<lbrakk>f (a::real) \<le> (y::real); y \<le> f b; a \<le> b; 
    \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x\<rbrakk>
   \<Longrightarrow> \<exists>x. f x = y"
by (frule IVT [of f]) auto

lemma inj_on_powreal: 
   "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> inj_on (\<lambda>x. a pow\<^sub>\<real> x) UNIV"
by (auto simp add: inj_on_def)

lemma LIMSEQ_powreal_minus_nat:
  "a > 1 \<Longrightarrow> (\<lambda>n. a pow\<^sub>\<real> (-real n)) \<longlonglongrightarrow> 0"
by (simp add: powreal_minus powreal_power_eq  
        LIMSEQ_inverse_realpow_zero)

lemma LIMSEQ_less_Ex:
   "\<lbrakk> X \<longlonglongrightarrow> (x::real); x < y \<rbrakk> \<Longrightarrow> \<exists>n. X n < y"
  by (meson LIMSEQ_le_const not_less)

lemma powreal_IVT_upper_lemma:
  assumes "a > (1::real)" and "x > 0" 
  shows "\<exists>n::nat. a pow\<^sub>\<real> (-real n) < x"
proof -
  have "(\<lambda>n. a pow\<^sub>\<real> - real n) \<longlonglongrightarrow> 0"
    by (simp add: LIMSEQ_powreal_minus_nat assms(1))
  then show ?thesis
    using LIMSEQ_less_Ex assms(2) by blast 
qed

lemma powreal_IVT_lower_lemma:
  assumes "a > (1::real)" 
  and "x > 0" 
  shows "\<exists>n::nat. x < a pow\<^sub>\<real> (real n)"
proof -
  have invx0: "0 < inverse x"
    by (simp add: assms(2)) 
  then have "\<exists>n. a pow\<^sub>\<real> - real n < inverse x"
    using assms(1) powreal_IVT_upper_lemma by blast
  then show ?thesis
    using assms(1) 
    by (auto dest: inverse_less_imp_less 
         simp add: powreal_minus powreal_gt_zero )
qed

lemma powreal_surj:
  assumes "a > 1" 
  and "x > 0" 
  shows "\<exists>y. a pow\<^sub>\<real> y = x"
proof -
  obtain n where "a pow\<^sub>\<real> - real n < x"
    using assms powreal_IVT_upper_lemma by blast 
  moreover obtain na where "x < a pow\<^sub>\<real> real na"
    using assms powreal_IVT_lower_lemma by blast 
  moreover have "\<forall>x. - real n \<le> x \<and> x \<le> real na \<longrightarrow> isCont ((pow\<^sub>\<real>) a) x"
    using assms(1) isCont_powreal_exponent_gt_one by blast
  ultimately show ?thesis 
    using IVT_simple [of _ "-real n" _ "real na"] by force
qed

lemma powreal_surj2:
    "\<lbrakk> 0 < a; a < 1; x > 0 \<rbrakk> \<Longrightarrow> \<exists>y. a pow\<^sub>\<real> y = x"
  using powreal_minus_base_ge_one powreal_surj real_inverse_gt_one_lemma 
  by blast

lemma powreal_ex1_eq:
  assumes "a > 0"
  and "a \<noteq> 1" 
  and "x > 0" 
  shows "\<exists>! y. a pow\<^sub>\<real> y = x"
proof (cases "a < 1")
  case True
  then show ?thesis 
    using assms powreal_inject powreal_surj2 by blast
next
  case False
  then show ?thesis
    using assms(2) assms(3) powreal_surj by auto 
qed

lemma powreal_Log_cancel [simp]:
   "\<lbrakk> a > 0; a \<noteq> 1; x > 0 \<rbrakk> \<Longrightarrow> a pow\<^sub>\<real> (Log a x) = x"
by (auto intro: the1I2 [OF powreal_ex1_eq] simp add: Log_def)

lemma Log_powreal_cancel [simp]: 
  "\<lbrakk> 0 < a; a \<noteq> 1 \<rbrakk> \<Longrightarrow> Log a (a pow\<^sub>\<real> y) = y"
by (metis powreal_ex1_eq powreal_gt_zero powreal_Log_cancel)

lemma Log_mult: 
     "\<lbrakk> 0 < a; a \<noteq> 1; 0 < x; 0 < y \<rbrakk>
      \<Longrightarrow> Log a (x * y) = Log a x + Log a y"
  by (metis Log_powreal_cancel powreal_Log_cancel powreal_add)

lemma Log_one [simp]: "\<lbrakk> 0 < a; a \<noteq> 1 \<rbrakk> \<Longrightarrow> Log a 1 = 0"
by (metis Log_powreal_cancel powreal_zero_eq_one)

lemma Log_eq_one [simp]: "\<lbrakk> 0 < a; a \<noteq> 1 \<rbrakk> \<Longrightarrow> Log a a = 1"
  using powreal_inject by fastforce

lemma Log_inverse:
  "\<lbrakk> a > 0; a \<noteq> 1; x > 0 \<rbrakk> \<Longrightarrow> Log a (inverse x) = - Log a x"
by (metis Log_powreal_cancel powreal_Log_cancel powreal_minus)

lemma Log_divide: 
  "\<lbrakk> 0 < a; a \<noteq> 1; 0 < x; 0 < y \<rbrakk>
   \<Longrightarrow> Log a (x/y) = Log a x - Log a y"
  by (metis Log_inverse Log_mult divide_real_def 
       inverse_positive_iff_positive minus_real_def)

lemma Log_less_cancel_iff [simp]:
  assumes "1 < a" 
  and "0 < x"
  and "0 < y"
shows "(Log a x < Log a y) = (x < y)"
proof
  assume "Log a x < Log a y" 
  then show "x < y" using powreal_Log_cancel assms powreal_less_cancel_iff 
    by (metis less_irrefl real_inverse_bet_one_one_lemma 
          inverse_positive_iff_positive)
next
  assume "x < y" 
  then show "Log a x < Log a y"
    using assms(1) assms(2) powreal_less_cancel_iff by fastforce 
qed

lemma Log_inj: assumes "1 < b" shows "inj_on (Log b) {0 <..}"
proof (rule inj_onI, simp)
  fix x y assume pos: "0 < x" "0 < y" and *: "Log b x = Log b y"
  show "x = y"
  proof (cases rule: linorder_cases)
    assume "x < y" hence "Log b x < Log b y"
      using Log_less_cancel_iff[OF \<open>1 < b\<close>] pos by simp
    thus ?thesis using * by simp
  next
    assume "y < x" hence "Log b y < Log b x"
      using Log_less_cancel_iff[OF \<open>1 < b\<close>] pos by simp
    thus ?thesis using * by simp
  qed simp
qed

lemma Log_le_cancel_iff [simp]:
     "\<lbrakk> 1 < a; 0 < x; 0 < y \<rbrakk> \<Longrightarrow> (Log a x \<le> Log a y) = (x \<le> y)"
by (simp add: linorder_not_less [symmetric])

lemma zero_less_Log_cancel_iff [simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < Log a x \<longleftrightarrow> 1 < x"
  using Log_less_cancel_iff[of a 1 x] by simp

lemma zero_le_Log_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 \<le> Log a x \<longleftrightarrow> 1 \<le> x"
  using Log_le_cancel_iff[of a 1 x] by simp

lemma Log_less_zero_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> Log a x < 0 \<longleftrightarrow> x < 1"
  using Log_less_cancel_iff[of a x 1] by simp

lemma Log_le_zero_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> Log a x \<le> 0 \<longleftrightarrow> x \<le> 1"
  using Log_le_cancel_iff[of a x 1] by simp

lemma one_less_Log_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 1 < Log a x \<longleftrightarrow> a < x"
  using Log_less_cancel_iff[of a a x] by simp

lemma one_le_Log_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 1 \<le> Log a x \<longleftrightarrow> a \<le> x"
  using Log_le_cancel_iff[of a a x] by simp

lemma Log_less_one_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> Log a x < 1 \<longleftrightarrow> x < a"
  using Log_less_cancel_iff[of a x a] by simp

lemma Log_le_one_cancel_iff[simp]: 
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> Log a x \<le> 1 \<longleftrightarrow> x \<le> a"
  using Log_le_cancel_iff[of a x a] by simp

lemma Log_powreal: 
  assumes "0 < x" 
  and "1 < b"
  and "b \<noteq> 1" 
shows "Log b (x pow\<^sub>\<real> y) = y * Log b x"
proof -
  have "b pow\<^sub>\<real> (Log b x * y) = x pow\<^sub>\<real> y"
    using assms powreal_mult [symmetric] by simp
  moreover have "0 < x pow\<^sub>\<real> y"
    by (simp add: assms(1) powreal_gt_zero)
  ultimately have "b pow\<^sub>\<real> (y * Log b x) = b pow\<^sub>\<real> Log b (x pow\<^sub>\<real> y)"
    using powreal_Log_cancel assms powreal_Log_cancel
    by (simp add: mult.commute)
  then show ?thesis
    using assms(2) powreal_inject_exp1 by blast 
qed

lemma Log_nat_power: 
  assumes "0 < x" 
  and "1 < b" and "b \<noteq> 1"
  shows " Log b (x ^ n) = real n * Log b x"
proof -
  have "Log b (x pow\<^sub>\<real> real n) = real n * Log b x"
    by (simp add: Log_powreal assms) 
  then show ?thesis
    by (simp add: assms(1) powreal_power_eq) 
qed

end