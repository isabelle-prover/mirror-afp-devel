section \<open>Exponentiation is Diophaninte\<close>

subsection \<open>Expressing Exponentiation in terms of the alpha function\<close>

theory Exponentiation
  imports "HOL-Library.Discrete"
begin

locale Exp_Matrices
  begin

subsubsection \<open>2x2 matrices and operations\<close>
datatype mat2 = mat (mat_11 : int) (mat_12 : int) (mat_21 : int) (mat_22 : int)
datatype vec2 = vec (vec_1: int) (vec_2: int)

fun mat_plus:: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where 
  "mat_plus A B = mat (mat_11 A + mat_11 B) (mat_12 A + mat_12 B) 
                      (mat_21 A + mat_21 B) (mat_22 A + mat_22 B)"

fun mat_mul:: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "mat_mul A B = mat (mat_11 A * mat_11 B + mat_12 A * mat_21 B) 
                     (mat_11 A * mat_12 B + mat_12 A * mat_22 B) 
                     (mat_21 A * mat_11 B + mat_22 A * mat_21 B) 
                     (mat_21 A * mat_12 B + mat_22 A * mat_22 B)"

fun mat_pow:: "nat \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "mat_pow 0 _ = mat 1 0 0 1" | 
  "mat_pow n A = mat_mul A (mat_pow (n - 1) A)"

lemma mat_pow_2[simp]: "mat_pow 2 A = mat_mul A A"
  by (simp add: numeral_2_eq_2)

fun mat_det::"mat2 \<Rightarrow> int" where
  "mat_det M = mat_11 M * mat_22 M - mat_12 M * mat_21 M"

fun mat_scalar_mult::"int \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "mat_scalar_mult a M = mat (a * mat_11 M) (a * mat_12 M) (a * mat_21 M) (a * mat_22 M)"

fun mat_minus:: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "mat_minus A B = mat (mat_11 A - mat_11 B) (mat_12 A - mat_12 B) 
                       (mat_21 A - mat_21 B) (mat_22 A - mat_22 B)"

fun mat_vec_mult:: "mat2 \<Rightarrow> vec2 \<Rightarrow> vec2" where
  "mat_vec_mult M v = vec (mat_11 M * vec_1 v + mat_12 M * vec_2 v) 
                          (mat_21 M * vec_1 v + mat_21 M * vec_2 v)"

definition ID :: "mat2" where "ID = mat 1 0 0 1"
declare mat_det.simps[simp del]

subsubsection \<open>Properties of 2x2 matrices\<close>
lemma mat_neutral_element: "mat_mul ID N = N" by (auto simp: ID_def)

lemma mat_associativity: "mat_mul (mat_mul D B) C = mat_mul D (mat_mul B C)"
  apply auto by algebra+ 

lemma mat_exp_law: "mat_mul (mat_pow n M) (mat_pow m M) = mat_pow (n+m) M" 
  apply (induction n, auto) by (metis mat2.sel(1,2) mat_associativity mat_mul.simps)+

lemma mat_exp_law_mult: "mat_pow (n*m) M = mat_pow n (mat_pow m M)" (is "?P n")
  apply (induction n, auto) using mat_exp_law by (metis mat_mul.simps)

lemma det_mult: "mat_det (mat_mul M1 M2) = (mat_det M1) * (mat_det M2)"
  by (auto simp: mat_det.simps algebra_simps)

subsubsection \<open>Special second-order recurrent sequences\<close>
text \<open>Equation 3.2\<close>
fun \<alpha>:: "nat \<Rightarrow> nat \<Rightarrow> int" where
           "\<alpha> b 0 = 0" | 
           "\<alpha> b (Suc 0) = 1" |
  alpha_n: "\<alpha> b (Suc (Suc n)) = (int b) * (\<alpha> b (Suc n)) - (\<alpha> b n)"

text \<open>Equation 3.3\<close>
lemma alpha_strictly_increasing:
  shows "int b \<ge> 2 \<Longrightarrow> \<alpha> b n < \<alpha> b (Suc n) \<and> 0 < \<alpha> b (Suc n)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have pos: "0 < \<alpha> b (Suc n)" by (simp add:Suc)
  have "\<alpha> b (Suc n) \<le> (int b) * (\<alpha> b (Suc n)) - \<alpha> b (Suc n)" using pos Suc by simp
  also have "... < \<alpha> b (Suc (Suc n))" by (simp add: Suc)
  finally show ?case using pos Suc by simp
qed

lemma alpha_strictly_increasing_general:
  fixes b n m::nat
  assumes "b > 2 \<and> m > n"
  shows "\<alpha> b m > \<alpha> b n"
proof -
  from alpha_strictly_increasing assms have S2: "\<alpha> b n < \<alpha> b m"
    by (smt less_imp_of_nat_less lift_Suc_mono_less of_nat_0_less_iff pos2)
  show ?thesis using S2 by simp
qed


text \<open>Equation 3.4\<close>
lemma alpha_superlinear: "b > 2 \<Longrightarrow> int n \<le> \<alpha> b n"
  apply (induction n, auto) 
  by (smt Suc_1 alpha_strictly_increasing less_imp_of_nat_less of_nat_1 of_nat_Suc)

text \<open>A simple consequence that's often useful; could also be generalized to alpha using 
      alpha linear\<close>

lemma alpha_nonnegative:
  shows "b > 2 \<Longrightarrow> \<alpha> b n \<ge> 0"
  using of_nat_0_le_iff alpha_superlinear order_trans by blast

text \<open>Equation 3.5\<close>
lemma alpha_linear: "\<alpha> 2 n = n"
proof(induct n rule: nat_less_induct)
  case (1 n)
  have s0: "n=0 \<Longrightarrow> \<alpha> 2 n = n" by simp
  have s1: "n=1 \<Longrightarrow> \<alpha> 2 n = n" by simp
  note hyp = \<open>\<forall>m < n. \<alpha> 2 m = m\<close>
  from hyp have s2: "n>1 \<Longrightarrow> \<alpha> 2 (n-1) = n-1 \<and> \<alpha> 2 (n-2) = n-2" by simp
  have s3: "n>1 \<Longrightarrow> \<alpha> 2 (Suc (Suc (n-2))) = 2*\<alpha> 2 (Suc (n-2)) - \<alpha> 2 (n-2)" by simp
  have s4: "n>1 \<Longrightarrow> Suc (Suc (n-2)) = n" by simp
  have s5: "n>1 \<Longrightarrow> Suc (n-2) = n-1" by simp
  from s3 s4 s5 have s6: "n>1 \<Longrightarrow> \<alpha> 2 n = 2*\<alpha> 2 (n-1) - \<alpha> 2 (n-2)" by simp
  from s2 s6 have s7: "n>1 \<Longrightarrow> \<alpha> 2 n = 2*(n-1) - (n-2)" by simp
  from s7 have s8: "n>1 \<Longrightarrow> \<alpha> 2 n = n" by simp
  from s0 s1 s8 show ?case by linarith
qed

text \<open>Equation 3.6 (modified)\<close>
lemma alpha_exponential_1: "b > 0 \<Longrightarrow> int b ^ n \<le> \<alpha> (b + 1) (n+1)"
proof(induction n)
case 0
  thus ?case by(simp)
next
  case (Suc n)
  hence "((int b)*(int b)^n) \<le> (int b)*(\<alpha> (b+1) (n+1))" by simp
  hence r2: "((int b)^(Suc n)) \<le> (int (b+1))*(\<alpha> (b+1) (n+1)) - (\<alpha> (b+1) (n+1))" 
    by (simp add: algebra_simps)
  have "(int b+1) *(\<alpha> (b+1) (n+1)) - (\<alpha> (b+1) (n+1)) \<le> (int b+1)*(\<alpha> (b+1) (n+1)) - \<alpha> (b+1) n" 
    using alpha_strictly_increasing Suc by (smt Suc_eq_plus1 of_nat_0_less_iff of_nat_Suc)
  thus ?case using r2 by auto
qed

lemma alpha_exponential_2: "int b>2 \<Longrightarrow> \<alpha> b (n+1) \<le> (int b)^(n)"
proof(induction n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  hence s1: "\<alpha> b (n+2) \<le> (int b)^(n+1) - \<alpha> b n" by simp
  have "(int b)^(n+1) - (\<alpha> b n) \<le> (int b)^(n+1)" 
    using alpha_strictly_increasing Suc by (smt \<alpha>.simps(1) alpha_superlinear of_nat_1 of_nat_add 
                                            of_nat_le_0_iff of_nat_less_iff one_add_one)
  thus ?case using s1 by simp
qed

subsubsection \<open>First order relation\<close>
text \<open>Equation 3.7 - Definition of A\<close>
fun A :: "nat \<Rightarrow> nat \<Rightarrow> mat2" where
  "A b 0 = mat 1 0 0 1" | 
  A_n: "A b n = mat (\<alpha> b (n + 1)) (-(\<alpha> b n)) (\<alpha> b n) (-(\<alpha> b (n - 1)))"

text \<open>Equation 3.9 - Definition of B\<close>
fun B :: "nat \<Rightarrow> mat2" where
  "B b = mat (int b) (-1) 1 0"

declare A.simps[simp del]
declare B.simps[simp del]

text \<open>Equation 3.8\<close>
lemma A_rec: "b>2 \<Longrightarrow> A b (Suc n) = mat_mul (A b n) (B b)" 
  by (induction n, auto simp: A.simps B.simps)

text \<open>Equation 3.10\<close>
lemma A_pow: "b>2 \<Longrightarrow> A b n = mat_pow n (B b)"
  apply (induction n, auto simp: A.simps B.simps)
    subgoal by (smt A.elims Suc_eq_plus1 \<alpha>.simps \<alpha>.simps(2) mat2.sel)
    subgoal for n apply (cases "n=0", auto) 
      using A.simps(2)[of b "n-1"] gr0_conv_Suc mult.commute by auto
    subgoal by (metis A.simps(2) Suc_eq_plus1 \<alpha>.simps(2) mat2.sel(1) mat_pow.elims)
    subgoal by (metis A.simps(2) \<alpha>.simps(1) add.inverse_neutral mat2.sel(2) mat_pow.elims)
    done


subsubsection \<open>Characteristic equation\<close>
text \<open>Equation 3.11\<close>
lemma A_det: "b>2 \<Longrightarrow> mat_det (A b n) = 1"
  apply (auto simp: A_pow, induction n, simp add: mat_det.simps)
  using det_mult apply (auto simp del: mat_mul.simps) by (simp add: B.simps mat_det.simps)

text \<open>Equation 3.12\<close>
lemma alpha_det1:
  assumes "b>2"
  shows "(\<alpha> b (Suc n))^2 - (int b) * \<alpha> b (Suc n) * \<alpha> b n + (\<alpha> b n)^2 = 1"
proof(cases "n = 0")
  case True
  thus ?thesis by auto
next
  case False
  hence "A b n = mat (\<alpha> b (n + 1)) (-(\<alpha> b n)) (\<alpha> b n) (-(\<alpha> b (n - 1)))" using A.elims neq0_conv by blast
  hence "mat_det (A b n)  = (\<alpha> b n)^2 - (\<alpha> b (Suc n)) * \<alpha> b (n-1)" 
    apply (auto simp: mat_det.simps) by (simp add: power2_eq_square)
  moreover hence "... =  (\<alpha> b (Suc n))^2 - b * (\<alpha> b (Suc n)) * \<alpha> b n + (\<alpha> b n)^2"
    using False alpha_n[of b "n-1"] apply(auto simp add: algebra_simps)
    by (metis Suc_1 distrib_left mult.commute mult.left_commute power_Suc power_one_right)
  ultimately show ?thesis using A_det assms by auto
qed

text \<open>Equation 3.12\<close>
lemma alpha_det2:
  assumes "b>2" "n>0"
  shows "(\<alpha> b (n-1))^2 - (int b) * (\<alpha> b (n-1) * (\<alpha> b n)) + (\<alpha> b n)^2 = 1"
  using alpha_det1 assms by (smt One_nat_def Suc_diff_Suc diff_zero mult.commute mult.left_commute)

text \<open>Equations 3.14 to 3.17\<close>
lemma alpha_char_eq:
  fixes x y b:: nat
  shows  "(y < x \<and> x * x + y * y = 1 + b * x * y) \<Longrightarrow> (\<exists>m. int y = \<alpha> b m \<and> int x = \<alpha> b (Suc m))"
proof (induct y arbitrary: x rule:nat_less_induct)
  case (1 n)

  note pre = \<open>n < x \<and> (x * x + n * n = 1 + b * x * n)\<close>

  have h0: "int (x * x + n * n) = int (x * x) + int (n * n)" by simp
  from pre h0 have pre1: "int x * int x + int(n * n) = int 1 + int(b * x * n)" by simp

  have i0: "int (n * n) = int n * int n" by simp
  have i1: "int (b * x * n) = int b * int x * int n" by simp
  from pre1 i0 i1 have pre2: "int x * int x + int n * int n = 1 + int b * int x * int n" by simp

  from pre2 have j0: "int n * int n - 1 = int b * int x * int n - int x * int x" by simp
  have j1:"\<dots> = int x * (int b * int n - int x)" by (simp add: right_diff_distrib)
  from j0 j1 have pre3:"int n * int n - 1 = int x * (int b * int n - int x)" by simp

  have k0: "int n * int n - 1 < int n * int n" by simp
  from pre3 k0 have k1:"int n * int n >  int x * (int b * int n - int x)" by simp
  from pre have k2: "int n \<le> int x" by simp
  from k2 have k3: "int x * int n \<ge> int n * int n" by (simp add: mult_mono)
  from k1 k3 have k4: "int x * int n > int x * (int b * int n - int x)" by linarith
  from pre k4 have k5: "int n > int b * int n - int x" by simp

  from pre have l0:"n = 0 \<Longrightarrow> x = 1" by simp
  from l0 have l1: "n = 0 \<Longrightarrow> x = Suc 0" by simp
  from l1 have l2: "n = 0 \<Longrightarrow> int n = \<alpha> b 0 \<and> int x = \<alpha> b (Suc 0)" by simp
  from l2 have l3: "n = 0 \<Longrightarrow> \<exists>m. int n = \<alpha> b m \<and> int x = \<alpha> b (Suc m)" by blast

  have m0: "n > 0 \<Longrightarrow> int n * int n - 1 \<ge> 0" by simp
  from pre3 m0 have m1: "n > 0 \<Longrightarrow> int x * (int b * int n - int x) \<ge> 0" by simp
  from m1 have m2: "n > 0 \<Longrightarrow> int b * int n - int x \<ge> 0" using zero_le_mult_iff by force

  from j0 have n0: "int x * int x - int b * int x * int n + int n * int n = 1" by simp
  have n1: "(int b * int n - int x) * (int b * int n - int x) = int b * int n * (int b * int n - int x) - int x * (int b * int n - int x)" by (simp add: left_diff_distrib)
  from n1 have n2: "int n * int n - int b * int n * (int b * int n - int x) + (int b * int n - int x) * (int b * int n - int x) = int n * int n - int x * (int b * int n - int x)" by simp
  from n0 n2 j1 have n3: "int n * int n - int b * int n * (int b * int n - int x) + (int b * int n - int x) * (int b * int n - int x) = 1" by linarith
  from n3 have n4: "int n * int n + (int b * int n - int x) * (int b * int n - int x) = 1 + int b * int n * (int b * int n - int x)" by simp
  have n5: "int b * int n = int (b * n)" by simp
  from n5 m2 have n6: "n > 0 \<Longrightarrow> int b * int n - int x = int (b * n - x)" by linarith
  from n4 n6 have n7: "n > 0 \<Longrightarrow> int (n * n + (b * n - x) * (b * n - x)) = int (1 + b * n * (b * n - x))" by simp
  from n7 have n8: "n > 0 \<Longrightarrow> n * n + (b * n - x) * (b * n - x) = 1 + b * n * (b * n - x)" using of_nat_eq_iff by blast

  note hyp = \<open>\<forall>m<n. \<forall>x. m < x \<and> x * x + m * m = 1 + b * x * m \<longrightarrow>
          (\<exists>ma. int m = \<alpha> b ma \<and> int x = \<alpha> b (Suc ma))\<close>

  from k5 n6 n8 have o0: "n > 0 \<Longrightarrow> (b * n - x) < n \<and> n * n + (b * n - x) * (b * n - x) = 1 + b * n * (b * n - x)" by simp
  from o0 hyp have o1: "n > 0 \<Longrightarrow> (\<exists>ma. int (b * n - x) = \<alpha> b ma \<and> int n = \<alpha> b (Suc ma))" by simp

  from o1 l3 n6 show ?case by force
qed

lemma alpha_char_eq2:
  assumes "(x*x + y*y = 1 + b * x * y)" "b>2"
  shows  "(\<exists>n. int x = \<alpha> b n)"
proof -
  have "x \<noteq> y"
  proof(rule ccontr, auto)
    assume "x=y"
    hence "2*x*x = 1+b*x*x" using assms by simp
    hence "2*x*x \<ge> 1+2*x*x" using assms by (metis add_le_mono le_less mult_le_mono1)
    thus False by auto
  qed
  thus ?thesis
  proof(cases "x<y")
    case True
    hence "\<exists>n. int x = \<alpha> b n \<and> int y = \<alpha> b (Suc n)" using alpha_char_eq assms
      by (simp add: add.commute power2_eq_square)
    thus ?thesis by auto
  next
    case False
    hence "\<exists>j. int y = \<alpha> b j \<and> int x = \<alpha> b (Suc j)" using alpha_char_eq assms \<open>x \<noteq> y\<close> by auto
    thus ?thesis by blast
  qed
qed


subsubsection \<open>Divisibility properties\<close>
text \<open>The following lemmas are needed in the proof of equation 3.25\<close>
lemma representation:
  fixes k m :: nat
  assumes "k > 0" "n = m mod k" "l = (m-n)div k"
  shows "m = n+k*l \<and> 0\<le>n \<and> n\<le>k-1" by (metis Suc_pred' assms le_add2 le_add_same_cancel2 
      less_Suc_eq_le minus_mod_eq_div_mult minus_mod_eq_mult_div mod_div_mult_eq
      mod_less_divisor neq0_conv nonzero_mult_div_cancel_left)

lemma div_3251:
  fixes b k m:: nat
  assumes "b>2" and "k>0"
  defines "n \<equiv> m mod k"
  defines "l \<equiv> (m-n) div k"
  shows "A b m = mat_mul (A b n) (mat_pow l (A b k))"
proof -
  from assms(2) l_def n_def representation have m: "m = n+k*l \<and> 0\<le>n \<and> n\<le>k-1" by simp
  from A_pow assms(1) have Abm2: "A b m = mat_pow m (B b)" by simp
  from m have Bm: "mat_pow m (B b) =mat_pow (n+k*l) (B b)" by simp
  from mat_exp_law have as1: "mat_pow (n+k*l) (B b) 
                            = mat_mul (mat_pow n (B b)) (mat_pow (k*l) (B b))" by simp
  from mat_exp_law_mult have as2: "mat_pow (k*l) (B b) = mat_pow l (mat_pow k (B b))" 
    by (metis mult.commute)
  from A_pow assms have Abn: "mat_pow n (B b) = A b n" by simp
  from A_pow assms(1) have Ablk: "mat_pow l (mat_pow k (B b)) = mat_pow l (A b k)" by simp
  from Ablk Abm2 Abn Bm as1 as2 show Abm: "A b m = mat_mul (A b n) (mat_pow l (A b k))" by simp
qed

lemma div_3252:
  fixes a b c d m :: int and l :: nat
  defines "M \<equiv> mat a b c d"
  assumes "mat_21 M mod m = 0"
  shows "(mat_21 (mat_pow l M)) mod m = 0 " (is "?P l")
proof(induction l)
  show "?P 0" by simp
next
  fix l assume IH: "?P l"
  define Ml where "Ml = mat_pow l M"
  have S1: "mat_pow (Suc(l)) M = mat_mul M (mat_pow l M)" by simp
  have S2: "mat_21 (mat_mul M Ml) = mat_21 M * mat_11 Ml + mat_22 M * mat_21 Ml" 
    by (rule_tac mat_mul.induct mat_plus.induct, auto)
  have S3: "mat_21 (mat_pow (Suc(l)) M) = mat_21 M * mat_11 Ml + mat_22 M * mat_21 Ml" 
    using S1 S2 Ml_def by simp
  from assms(2) have S4: "(mat_21 M * mat_11 Ml) mod m = 0" by auto
  from IH Ml_def have S5: " mat_22 M * mat_21 Ml mod m = 0" by auto
  from S4 S5 have S6: "(mat_21 M * mat_11 Ml + mat_22 M * mat_21 Ml) mod m = 0" by auto
  from S3 S6 show "?P (Suc(l))" by simp
qed

lemma div_3253:
  fixes a b c d m:: int and l :: nat
  defines "M \<equiv> mat a b c d"
  assumes "mat_21 M mod m = 0"
  shows "((mat_11 (mat_pow l M)) - a^l) mod m = 0" (is "?P l")
proof(induction l)
  show "?P 0" by simp
next
  fix l assume IH: "?P l"
  define Ml where "Ml = mat_pow l M"
  from Ml_def have S1: "mat_pow (Suc(l)) M = mat_mul M Ml" by simp
  have S2: "mat_11 (mat_mul M Ml) = mat_11 M * mat_11 Ml + mat_12 M * mat_21 Ml" 
    by (rule_tac mat_mul.induct mat_plus.induct, auto)
  hence S3: "mat_11 (mat_pow (Suc(l)) M) = mat_11 M * mat_11 Ml + mat_12 M * mat_21 Ml" 
    using S1 by simp
  from M_def Ml_def assms(2) div_3252 have S4: "mat_21 Ml mod m = 0" by auto
  from IH Ml_def have S5: "(mat_11 Ml - a ^ l) mod m = 0" by auto
  from IH M_def have S6: "(mat_11 M -a) mod m = 0" by simp
  from S4 have S7: "(mat_12 M * mat_21 Ml) mod m = 0" by auto
  from S5 S6 have S8: "(mat_11 M * mat_11 Ml- a^(Suc(l))) mod m = 0" 
  by (metis M_def mat2.sel(1) mod_0 mod_mult_right_eq mult_zero_right power_Suc right_diff_distrib)
  have S9: "(mat_11 M * mat_11 Ml - a^(Suc(l)) + mat_12 M * mat_21 Ml ) mod m = 0" 
    using S7 S8 by auto
  from S9 have S10: "(mat_11 M * mat_11 Ml + mat_12 M * mat_21 Ml - a^(Suc(l))) mod m = 0" by smt
  from S3 S10 show "?P (Suc(l))" by auto
qed

text \<open>Equation 3.25\<close>
lemma divisibility_lemma1:
    fixes b k m:: nat
  assumes "b>2" and "k>0"
  defines "n \<equiv> m mod k"
  defines "l \<equiv> (m-n) div k"
  shows "\<alpha> b m mod \<alpha> b k = \<alpha> b n * (\<alpha> b (k+1)) ^ l mod \<alpha> b k"
proof -
  from assms(2) l_def n_def representation have m: "m = n+k*l \<and> 0\<le>n \<and> n\<le>k-1" by simp
  consider (eq0) "n = 0" | (neq0) "n > 0" by auto
  thus ?thesis
  proof cases
    case eq0
    have Abm_gen: "A b m = mat_mul (A b n) (mat_pow l (A b k))" 
      using assms div_3251 l_def n_def by blast
    have Abk: "mat_pow l (A b k) = mat_pow l (mat (\<alpha> b (k+1)) (-\<alpha> b k) (\<alpha> b k) (-\<alpha> b (k-1)))" 
      using assms(2) neq0_conv by (metis A.elims)
    from eq0 have Abm: "A b m = mat_pow l (mat (\<alpha> b (k+1)) (-\<alpha> b k) (\<alpha> b k) (-\<alpha> b (k-1)))" 
      using A_pow \<open>b>2\<close> apply (auto simp: A.simps B.simps)
      by (metis Abk Suc_eq_plus1 add.left_neutral m mat_exp_law_mult mult.commute)
    have Abm1: "mat_21 (A b m) = \<alpha> b m" by (metis A.elims \<alpha>.simps(1) mat2.sel(3))
    have Abm2: "mat_21 (mat_pow l (mat (\<alpha> b (k+1)) (-\<alpha> b k) (\<alpha> b k) (-\<alpha> b (k-1)))) mod (\<alpha> b k) = 0" 
      using Abm div_3252 by simp
    from Abm Abm1 Abm2 have MR0: "\<alpha> b m mod \<alpha> b k = 0" by simp
    from MR0 eq0 show ?thesis by simp
  next case neq0
    from assms have Abm_gen: "A b m = mat_mul (A b n) (mat_pow l (A b k))" 
      using div_3251 l_def n_def by blast
    from assms(2) neq0_conv have Abk: "mat_pow l (A b k) 
               = mat_pow l (mat (\<alpha> b (k+1)) (-\<alpha> b k) (\<alpha> b k) (-\<alpha> b (k-1)))" by (metis A.elims)
  from n_def neq0 have N0: "n>0" by simp
  define M where "M = mat (\<alpha> b (n + 1)) (-(\<alpha> b n)) (\<alpha> b n) (-(\<alpha> b (n - 1)))"
  define N where "N = mat_pow l (mat (\<alpha> b (k+1)) (-\<alpha> b k) (\<alpha> b k) (-\<alpha> b (k-1)))"
  from Suc_pred' neq0 have Abn: "A b n = mat (\<alpha> b (n + 1)) (-(\<alpha> b n)) (\<alpha> b n) (-(\<alpha> b (n - 1)))" 
    by (metis A.elims neq0_conv)
  from Abm_gen Abn Abk M_def N_def have Abm: "A b m = mat_mul M N" by simp
  (* substitutions done! next: calculations *)
  from Abm have S1: "mat_21 (mat_mul M N) = mat_21 M * mat_11 N + mat_22 M * mat_21 N" 
    by (rule_tac mat_mul.induct mat_plus.induct, auto)
  have S2: "mat_21 (A b m) = \<alpha> b m" by (metis A.elims \<alpha>.simps(1) mat2.sel(3))
  from S1 S2 Abm have S3: "\<alpha> b m = mat_21 M * mat_11 N + mat_22 M * mat_21 N" by simp
  from S3 have S4: "(\<alpha> b m - (mat_21 M * mat_11 N + mat_22 M * mat_21 N)) mod (\<alpha> b k) = 0" by simp
  from M_def have S5: "mat_21 M = \<alpha> b n" by simp
  from div_3253 N_def have S6: "(mat_11 N - (\<alpha> b (k+1)) ^ l) mod (\<alpha> b k) = 0" by simp
  from N_def Abm div_3252 have S7: "mat_21 N mod (\<alpha> b k) = 0" by simp
  from S4 S7 have S8: "(\<alpha> b m - mat_21 M * mat_11 N) mod (\<alpha> b k) = 0" by algebra
  from S5 S6 have S9: "(mat_21 M * mat_11 N - (\<alpha> b n) * (\<alpha> b (k+1)) ^ l) mod (\<alpha> b k) = 0"
    by (metis mod_0 mod_mult_left_eq mult.commute mult_zero_left right_diff_distrib')
  from S8 S9 show ?thesis
  proof -
    have "(mat_21 M * mat_11 N - \<alpha> b m) mod \<alpha> b k = 0"
      using S8 by presburger
    hence "\<forall>i. (\<alpha> b m - (mat_21 M * mat_11 N - i)) mod \<alpha> b k = i mod \<alpha> b k"
      by (metis (no_types) add.commute diff_0_right diff_diff_eq2 mod_diff_right_eq)
    thus ?thesis
      by (metis (no_types) S9 diff_0_right mod_diff_right_eq)
  qed
    qed
  qed

text \<open>Prerequisite lemma for 3.27\<close>
lemma div_coprime:
  assumes "b>2" "n \<ge> 0"
    shows "coprime (\<alpha> b k) (\<alpha> b (k+1))" (is "?P")
proof(rule ccontr)
  assume as: "\<not> ?P"
  define n where "n = gcd (\<alpha> b k) (\<alpha> b (k+1))"
  from n_def have S1: "n > 1"
    using alpha_det1 as assms(1) coprime_iff_gcd_eq_1 gcd_pos_int right_diff_distrib' 
    by (smt add.commute plus_1_eq_Suc)
  have S2: "(\<alpha> b (Suc k))^2 - (int b) * \<alpha> b (Suc k) * (\<alpha> b k) + (\<alpha> b k)^2 = 1" 
    using alpha_det1 assms by auto
  from n_def have D1: " n dvd (\<alpha> b (k+1))^2" by (simp add: numeral_2_eq_2)
  from n_def have D2: " n dvd (- (int b) * \<alpha> b (k+1) * (\<alpha> b k))" by simp
  from n_def have D3: "n dvd (\<alpha> b k)^2" by (simp add: gcd_dvdI1)
  have S3: "n dvd ((\<alpha> b (Suc k))^2 - (int b) * \<alpha> b (Suc k) * (\<alpha> b k) + (\<alpha> b k)^2)" 
    using D1 D2 D3 by simp
  from S2 S3 have S4: "n dvd 1" by simp
  from S4 n_def as is_unit_gcd show "False" by blast
qed

text \<open>Equation 3.27\<close>
lemma divisibility_lemma2:
  fixes b k m:: nat
  assumes "b>2" and "k>0"
  defines "n \<equiv> m mod k"
  defines "l \<equiv> (m-n) div k"
  assumes "\<alpha> b k dvd \<alpha> b m"
    shows "\<alpha> b k dvd \<alpha> b n"
proof -
  from assms(2) l_def n_def representation have m: "0\<le>n \<and> n\<le>k-1" by simp
  from divisibility_lemma1 assms(1) assms(2) l_def n_def have S1: 
    "(\<alpha> b m) mod (\<alpha> b k)  = (\<alpha> b n) * (\<alpha> b (k+1)) ^ l mod (\<alpha> b k)" by blast
  from S1 assms(5) have S2: "(\<alpha> b k) dvd ((\<alpha> b n) * (\<alpha> b (k+1)) ^ l)" by auto
  show ?thesis
    using S1 div_coprime S2 assms(1) apply auto
    using coprime_dvd_mult_left_iff coprime_power_right_iff by blast  
qed

text \<open>Equation 3.23 - main result of this section\<close>
theorem divisibility_alpha:
  assumes "b>2" and "k>0"
    shows "\<alpha> b k dvd \<alpha> b m \<longleftrightarrow> k dvd m" (is "?P \<longleftrightarrow> ?Q")
proof
  assume Q: "?Q"
  define n where "n = m mod k"
  have N: "n=0" by (simp add: Q n_def)
  from N have Abn: "\<alpha> b n = 0" by simp
  from Abn divisibility_lemma1 assms(1) assms(2) mult_eq_0_iff n_def show "?P"
    by (metis dvd_0_right dvd_imp_mod_0 mod_0_imp_dvd) 
next 
  assume P: "?P"
  define n where "n = m mod k"
  define l where "l = (m-n) div k"
  define B where "B = (mat (int b) (-1) 1 0)"
  have S1: "(\<alpha> b n) mod (\<alpha> b k) = 0" 
    using divisibility_lemma2 assms(1) assms(2) n_def P by simp
  from n_def assms(2) have m: "n < k" using mod_less_divisor by blast
  from alpha_strictly_increasing m assms(1) have S2: "\<alpha> b n < \<alpha> b k"
    by (smt less_imp_of_nat_less lift_Suc_mono_less of_nat_0_less_iff pos2)
  from S1 S2 have S3: "n=0"
    by (smt alpha_superlinear assms(1) mod_pos_pos_trivial neq0_conv of_nat_0_less_iff)
  from S3 n_def show "?Q" by auto
qed

subsubsection \<open>Divisibility properties (continued)\<close>

text \<open>Equation 3.28 - main result of this section\<close>

lemma divisibility_equations:
  assumes 0: "m = k*l" and "b>2" "m>0"
  shows  "A b m = mat_pow l (mat_minus (mat_scalar_mult (\<alpha> b k) (B b)) 
                                        (mat_scalar_mult (\<alpha> b (k-1)) ID))"
    apply (auto simp del: mat_pow.simps mat_mul.simps mat_minus.simps mat_scalar_mult.simps
                simp add: A_pow mult.commute[of k l] assms mat_exp_law_mult)
    using A_pow[of b k] \<open>m>0\<close>
    apply (auto simp: A.simps \<open>m>0\<close> ID_def B.simps) 
    using A.simps(2) alpha_n One_nat_def Suc_eq_plus1 Suc_pred assms \<open>m>0\<close> assms
        mult.commute nat_0_less_mult_iff
    by (smt mat_exp_law_mult)

lemma divisibility_cong:
  fixes e f :: int
  fixes l :: nat
  fixes M :: mat2
  assumes "mat_22 M = 0" "mat_21 M = 1"
  shows "(mat_21 (mat_pow l (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID)))) mod e^2 = (-1)^(l-1)*l*e*f^(l-1)*(mat_21 M) mod e^2
        \<and> mat_22  (mat_pow l (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))) mod e^2 = (-1)^l *f^l mod e^2" 
(is "?P l \<and> ?Q l" )
proof(induction l)
  case 0
  then show ?case by simp
next
  case (Suc l)
  have S2: "mat_pow (Suc(l)) (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID)) =
    mat_mul (mat_pow l (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))) (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))"
    using mat_exp_law[of l _ 1] mat2.sel by (auto, metis)+
  define a1 where "a1 = mat_11 (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))"
  define b1 where "b1 = mat_12 (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))"
  define c1 where "c1 = mat_21 (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))"
  define d1 where "d1 = mat_22 (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))"
  define a where "a = mat_11 M"
  define b where "b = mat_12 M"
  define c where "c = mat_21 M"
  define d where "d = mat_22 M"
  define g where "g = mat_21 (mat_pow l (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID)))"
  define h where "h = mat_22 (mat_pow l (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID)))"
  from S2 g_def a1_def h_def c1_def have S3: "mat_21 (mat_pow (Suc(l)) (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID))) = g*a1 + h*c1"
    by simp
  from S2 g_def b1_def h_def d1_def have S4: "mat_22 (mat_pow (Suc(l)) (mat_minus (mat_scalar_mult e M) (mat_scalar_mult f ID)))
    = g*b1+h*d1" by simp
  have S5: "mat_11 (mat_scalar_mult e M) = e*a" by (simp add: a_def)
  have S6: "mat_12 (mat_scalar_mult e M) = e*b" by (simp add: b_def)
  have S7: "mat_21 (mat_scalar_mult e M) = e*c" by (simp add: c_def)
  have S8: "mat_22 (mat_scalar_mult e M) = e*d" by (simp add: d_def)
  from a1_def S5  have S9: "a1 = e*a-f"by (simp add: Exp_Matrices.ID_def)
  from b1_def S6  have S10: "b1 = e*b" by (simp add: Exp_Matrices.ID_def)
  from c1_def S7  have S11: "c1 = e*c" by (simp add: Exp_Matrices.ID_def)
  from S11 assms(2) c_def have S115: "c1 = e" by simp
  from d1_def S8  have S12: "d1 = e*d - f" by (simp add: Exp_Matrices.ID_def)
  from S12 assms(1) d_def have S125: "d1 = - f" by simp
  from assms(2) c_def Suc g_def c_def have S13: "g mod e^2 = (-1)^(l-1)*l*e*f^(l-1)*c mod e^2" by blast
  from assms(2) c_def S13 have S135: "g mod e^2 = (-1)^(l-1)*l*e*f^(l-1) mod e^2" by simp
  from Suc h_def have S14: "h mod e^2 = (-1)^l *f^l mod e^2" by simp
  from S10 S135 have S27: "g*b1 mod e^2 = (-1)^(l-1)*l*e*f^(l-1)*e*b mod e^2" by (metis mod_mult_left_eq mult.assoc)
  from S27 have S28: "g*b1 mod e^2 = 0 mod e^2" by (simp add: power2_eq_square)
  from S125 S14 mod_mult_cong have S29: "h*d1 mod e^2 = (-1)^l *f^l*(- f) mod e^2" by blast
  from S29 have S30: "h*d1 mod e^2 = (-1)^(l+1) *f^l*f mod e^2" by simp
  from S30 have S31: "h*d1 mod e^2 = (-1)^(l+1) *f^(l+1) mod e^2" by (metis mult.assoc power_add power_one_right)
  from S31 have F2: "?Q (Suc(l))" by (metis S28 S4 Suc_eq_plus1 add.left_neutral mod_add_cong)
  from S9 S13 have S15: "g*a1 mod e^2 = ((-1)^(l-1)*l*e*f^(l-1)*c*(e*a-f))mod e^2" by (metis mod_mult_left_eq)
  have S16: "((-1)^(l-1)*l*e*f^(l-1)*c*(e*a-f)) = ((-1)^(l-1)*l*e^2*f^(l-1)*c*a) - f*(-1)^(l-1)*l*e*f^(l-1)*c" by algebra
  have S17: "((-1)^(l-1)*l*e^2*f^(l-1)*c*a) mod e^2 = 0 mod e^2" by simp
  from S17 have S18: "(((-1)^(l-1)*l*e^2*f^(l-1)*c*a) - f*(-1)^(l-1)*l*e*f^(l-1)*c) mod e^2 =
    - f*(-1)^(l-1)*l*e*f^(l-1)*c mod e^2"
    proof -
      have f1: "\<forall>i ia. (ia::int) - (0 - i) = ia + i"
        by auto
      have "\<forall>i ia. ((0::int) - ia) * i = 0 - ia * i"
        by auto
      then show ?thesis using f1
      proof -
        have f1: "\<And>i. (0::int) - i = - i"
          by presburger
        then have "\<And>i. (i - - ((- 1) ^ (l - 1) * int l * e\<^sup>2 * f ^ (l - 1) * c * a)) mod e\<^sup>2 = i mod e\<^sup>2"
          by (metis (no_types) S17 \<open>\<forall>i ia. ia - (0 - i) = ia + i\<close> add.right_neutral mod_add_right_eq)
        then have "\<And>i. ((- 1) ^ (l - 1) * int l * e\<^sup>2 * f ^ (l - 1) * c * a - i) mod e\<^sup>2 = - i mod e\<^sup>2"
          using f1 by (metis \<open>\<forall>i ia. ia - (0 - i) = ia + i\<close> uminus_add_conv_diff)
        then show ?thesis
          using f1 \<open>\<forall>i ia. (0 - ia) * i = 0 - ia * i\<close> by presburger
      qed
  qed
  from S15 S16 S18 have S19: "g*a1 mod e^2 = - f*(-1)^(l-1)*l*e*f^(l-1)*c mod e^2" by presburger
  from S11 S14 have S20: "h*c1 mod e^2 = (-1)^l *f^l*e*c mod e^2" by (metis mod_mult_left_eq mult.assoc)
  from S19 S20 have S21: "(g*a1 + h*c1) mod e^2 = (- f*(-1)^(l-1)*l*e*f^(l-1)*c + (-1)^l *f^l*e*c) mod e^2" using mod_add_cong by blast
  from assms(2) c_def have S22: "(- f*(-1)^(l-1)*l*e*f^(l-1)*c + (-1)^l *f^l*e*c) mod e^2=(- f*(-1)^(l-1)*l*e*f^(l-1) + (-1)^l *f^l*e) mod e^2" by simp
  have S23: "(- f*(-1)^(l-1)*l*e*f^(l-1) + (-1)^l *f^l*e) mod e^2 = (f*(-1)^(l)*l*e*f^(l-1) + (-1)^l *f^l*e) mod e^2"
    by (smt One_nat_def Suc_pred mult.commute mult_cancel_left2 mult_minus_left neq0_conv of_nat_eq_0_iff power.simps(2))
  have S24: "(f*(-1)^(l)*l*e*f^(l-1) + (-1)^l *f^l*e) mod e^2 = ((-1)^(l)*l*e*f^l + (-1)^l *f^l*e) mod e^2"
    by (smt One_nat_def Suc_pred mult.assoc mult.commute mult_eq_0_iff neq0_conv of_nat_eq_0_iff power.simps(2))
  have S25: "((-1)^(l)*l*e*f^l + (-1)^l *f^l*e) mod e^2 = ((-1)^(l)*(l+1)*e*f^l) mod e^2"
  proof -
    have f1: "\<forall>i ia. (ia::int) * i = i * ia"
      by simp
    then have f2: "\<forall>i ia. (ia::int) * i - - i = i * (ia - - 1)"
      by (metis (no_types) mult.right_neutral mult_minus_left right_diff_distrib')
    have "\<forall>n. int n - - 1 = int (n + 1)"
      by simp
    then have "e * (f ^ l * (int l * (- 1) ^ l - - ((- 1) ^ l))) mod e\<^sup>2 = e * (f ^ l * ((- 1) ^ l * int (l + 1))) mod e\<^sup>2"
      using f2 by presburger
    then have "((- 1) ^ l * int l * e * f ^ l - - ((- 1) ^ l) * f ^ l * e) mod e\<^sup>2 = (- 1) ^ l * int (l + 1) * e * f ^ l mod e\<^sup>2"
      using f1
    proof -
      have f1: "\<And>i ia ib. (i::int) * (ia * ib) = ia * (i * ib)"
        by simp
      then have "\<And>i ia ib. (i::int) * (ia * ib) - - (i * ib) = (ia - - 1) * (i * ib)"
        by (metis (no_types) \<open>\<forall>i ia. ia * i = i * ia\<close> f2)
      then show ?thesis
        using f1 by (metis (no_types) \<open>\<forall>i ia. ia * i = i * ia\<close> \<open>e * (f ^ l * (int l * (- 1) ^ l - - ((- 1) ^ l))) mod e\<^sup>2 = e * (f ^ l * ((- 1) ^ l * int (l + 1))) mod e\<^sup>2\<close> f2 mult_minus_right)
    qed
    then show ?thesis
      by simp
  qed
  from S21 S22 S23 S24 S25 have S26: "(g*a1 + h*c1) mod e^2 = ((-1)^(l)*(l+1)*e*f^l) mod e^2" by presburger
  from S3 S26 have F1: "?P (Suc(l))" by (metis Suc_eq_plus1 assms(2) diff_Suc_1 mult.right_neutral)
  from F1 F2 show ?case by simp
qed

lemma divisibility_congruence:
  assumes "m = k*l" and "b>2" "m>0"
  shows "\<alpha> b m mod (\<alpha> b k)^2 = ((-1)^(l-1)*l*(\<alpha> b k)*(\<alpha> b (k-1))^(l-1)) mod (\<alpha> b k)^2"
proof -
  have S0: "\<alpha> b m = mat_21 (A b m)" by (metis A.elims assms(3) mat2.sel(3) neq0_conv)
  from assms S0 divisibility_equations have S1: "\<alpha> b m =
    mat_21 ( mat_pow l (mat_minus (mat_scalar_mult (\<alpha> b k) (B b)) 
                                        (mat_scalar_mult (\<alpha> b (k-1)) ID)))" by auto
  have S2: "mat_21 (B b) = 1" using Binomial.binomial_ring by (simp add: Exp_Matrices.B.simps)
  have S3: "mat_22 (B b) = 0"  by (simp add: Exp_Matrices.B.simps)
  from S1 S2 S3 divisibility_cong show ?thesis by (metis mult.right_neutral)
qed

text \<open> Main result section 3.5 \<close>
theorem divisibility_alpha2:
  assumes "b>2" "m>0"
  shows "(\<alpha> b k)^2 dvd (\<alpha> b m) \<longleftrightarrow> k*(\<alpha> b k) dvd m" (is "?P \<longleftrightarrow> ?Q")
proof
  assume Q: "?Q"
  then show "?P"
  proof(cases "k dvd m")
    case True
    then obtain l where mkl: "m = k * l" by blast
    from Q assms mkl have S0: "l mod \<alpha> b k = 0" by simp
    from S0 have S1: "l*(\<alpha> b k) mod (\<alpha> b k)^2 = 0" by (simp add: power2_eq_square)
    from S1 have S2: "((-1)^(l-1)*l*(\<alpha> b k)*(\<alpha> b (k-1))^(l-1)) mod (\<alpha> b k)^2 = 0"
      proof -
        have "\<forall>i. \<alpha> b k * (int l * i) mod (\<alpha> b k)\<^sup>2 = 0"
          by (metis (no_types) S1 mod_0 mod_mult_left_eq mult.assoc mult.left_commute mult_zero_left)
        then show ?thesis
          by (simp add: mult.assoc mult.left_commute)
    qed
    from assms divisibility_congruence mkl have S3: 
      "\<alpha> b m mod (\<alpha> b k)^2 = ((-1)^(l-1)*l*(\<alpha> b k)*(\<alpha> b (k-1))^(l-1)) mod (\<alpha> b k)^2" by simp
    from S2 S3 have S4: "\<alpha> b m mod (\<alpha> b k)^2 = 0" by linarith
    then show ?thesis by auto
  next
    case False
    then show ?thesis using Q dvd_mult_left int_dvd_int_iff by blast
  qed
next 
  assume P: "?P"
  show "?Q" 
  proof(cases "k dvd m")
    case True
      then obtain l where mkl: "m = k * l" by blast
      from assms mkl divisibility_congruence have S0: 
          "\<alpha> b m mod (\<alpha> b k)^2 = ((-1)^(l-1)*l*(\<alpha> b k)*(\<alpha> b (k-1))^(l-1)) mod (\<alpha> b k)^2" by simp
      from S0 P have S1: "(\<alpha> b k)^2 dvd ((-1)^(l-1)*l*(\<alpha> b k)*(\<alpha> b (k-1))^(l-1))" by auto
      from S1 have S2: "(\<alpha> b k)^2 dvd l*(\<alpha> b k)*(\<alpha> b (k-1))^(l-1)"
        by (metis (no_types, opaque_lifting) Groups.mult_ac(1) dvd_trans dvd_triv_right left_minus_one_mult_self)
      from S2 have S3: "(\<alpha> b k) dvd l*(\<alpha> b (k-1))^(l-1)"
        by (metis (full_types) Exp_Matrices.alpha_superlinear assms(1) assms(2) mkl 
            mult.assoc mult.commute mult_0 not_less_zero of_nat_le_0_iff power2_eq_square zdvd_mult_cancel)
      from div_coprime Suc_eq_plus1 Suc_pred' assms(1) assms(2) mkl less_imp_le_nat nat_0_less_mult_iff
      have S4: "coprime (\<alpha> b k) (\<alpha> b (k-1))" by (metis coprime_commute)
      hence "coprime (\<alpha> b k) ((\<alpha> b (k-1))^(l-1))" using coprime_power_right_iff by blast
      hence "(\<alpha> b k) dvd l" using S3 using coprime_dvd_mult_left_iff by blast
      then show ?thesis by (simp add: mkl)
  next
    case False
    then show ?thesis 
      apply(cases "0<k")
      subgoal using divisibility_alpha[of b k m] assms using dvd_mult_left P by auto
      subgoal using Exp_Matrices.alpha_strictly_increasing_general assms(1) P by fastforce
    done
  qed
qed

subsubsection \<open>Congruence properties\<close>
text \<open>In this section we will need the inverse matrices of A and B\<close>
fun A_inv :: "nat \<Rightarrow> nat \<Rightarrow> mat2" where
  "A_inv b n = mat (-\<alpha> b (n-1)) (\<alpha> b n) (-\<alpha> b n) (\<alpha> b (n+1))"

fun B_inv :: "nat \<Rightarrow> mat2" where
  "B_inv b = mat 0 1 (-1) b"

lemma A_inv_aux: "b>2 \<Longrightarrow> n>0 \<Longrightarrow> \<alpha> b n * \<alpha> b n - \<alpha> b (Suc n) * \<alpha> b (n - Suc 0) = 1" 
  apply (induction n, auto) subgoal for n using alpha_det1[of b n] apply auto by algebra done

lemma A_inverse[simp]: "b>2 \<Longrightarrow> n>0 \<Longrightarrow> mat_mul (A_inv b n) (A b n) = ID"
  using mat2.expand[of "mat_mul (A_inv b n) (A b n)" ID] apply rule
  using ID_def A.simps(2)[of _ "n-1"] ID_def apply (auto) 
    subgoal using mat2.sel(1)[of 1 0 0 1] apply (auto) 
      using A_inv_aux[of b n] by (auto simp: mult.commute) 
    subgoal by (metis mat2.sel(2)) 
    subgoal by (metis mat2.sel(3))
    subgoal using mat2.sel(4)[of 1 0 0 1] apply (auto) 
          using A_inv_aux[of b n] by (auto simp: mult.commute) 
  done

lemma B_inverse[simp]: "mat_mul (B b) (B_inv b) = ID" using B.simps ID_def by auto

declare A_inv.simps B_inv.simps[simp del]


text \<open>Equation 3.33\<close>
lemma congruence:
  assumes "b1 mod q = b2 mod q"
  shows "\<alpha> b1 n mod q = \<alpha> b2 n mod q"
proof (induct n rule:nat_less_induct)
  case (1 n)
  note hyps = \<open>\<forall>m<n. \<alpha> b1 m mod q = \<alpha> b2 m mod q\<close>
  have n0:"(\<alpha> b1 0) mod q = (\<alpha> b2 0) mod q" by simp
  have n1:"(\<alpha> b1 1) mod q = (\<alpha> b2 1) mod q" by simp
  from hyps have s1: "n>1\<Longrightarrow>\<alpha> b1 (n-1) mod q = \<alpha> b2 (n-1) mod q" by auto
  from hyps have s2: "n>1\<Longrightarrow>\<alpha> b1 (n-2) mod q = \<alpha> b2 (n-2) mod q" by auto
  have s3: "n>1 \<Longrightarrow> \<alpha> b1 (Suc (Suc n)) = (int b1) * (\<alpha> b1 (Suc n)) - (\<alpha> b1 n)" by simp
  from s3 have s4: "n>1 \<Longrightarrow> (\<alpha> b1 n = (int b1*(\<alpha> b1 (n-1)) - \<alpha> b1 (n-2)))" 
    by (smt Suc_1 Suc_diff_Suc diff_Suc_1 alpha_n lessE)
  have sw: "n>1 \<Longrightarrow> \<alpha> b2 (Suc (Suc n)) = (int b2) * (\<alpha> b2 (Suc n)) - (\<alpha> b2 n)" by simp
  from sw have sx: "n>1 \<Longrightarrow> (\<alpha> b2 n = (int b2*(\<alpha> b2 (n-1)) - \<alpha> b2 (n-2)))" 
    by (smt Suc_1 Suc_diff_Suc diff_Suc_1 alpha_n lessE)
  from n0 n1 s1 s2 s3 s4 assms(1) mod_mult_cong have s5: "n>1 
        \<Longrightarrow> b1*(\<alpha> b1 (n-1)) mod q =  b2*(\<alpha> b2 (n-1)) mod q " by (smt mod_mult_eq of_nat_mod)
   from hyps have sq: "n>1 \<Longrightarrow> \<alpha> b1 (n-2) mod q = \<alpha> b2 (n-2) mod q " by simp
   from s5 sq have sd: "n>1 \<Longrightarrow>-( (\<alpha> b1 (n-2))) mod q = -((\<alpha> b2 (n-2))) mod q " 
     by (metis mod_minus_eq)
   from sd s5 mod_add_cong have s6: "n>1 \<Longrightarrow> ( b1*(\<alpha> b1 (n-1)) - \<alpha> b1 (n-2)) mod q  
                                      =  (b2*(\<alpha> b2 (n-1)) - \<alpha> b2 (n-2)) mod q" by force
  from s4 have sa: "n>1 \<Longrightarrow>( b1*(\<alpha> b1 (n-1)) - \<alpha> b1 (n-2)) mod q = (\<alpha> b1 n) mod q" by simp
  from sx have sb: "n>1 \<Longrightarrow>( b2*(\<alpha> b2 (n-1)) - \<alpha> b2 (n-2)) mod q = (\<alpha> b2 n) mod q" by simp
  from sb sa s6 sx have s7: "n>1 \<Longrightarrow> (\<alpha> b1 n) mod q = (b2*(\<alpha> b2 (n-1)) - \<alpha> b2 (n-2)) mod q" by simp
  from s7 sx s6 have s9: "\<alpha> b1 n mod q = \<alpha> b2 n mod q" 
    by (metis One_nat_def \<alpha>.simps(1) \<alpha>.simps(2) less_Suc0 nat_neq_iff)
  from s9 n0 n1 show ?case by simp
qed

text \<open>Equation 3.34\<close>
lemma congruence2:
  fixes b1 :: nat
  assumes "b>=2"
  shows "(\<alpha> b n) mod (b - 2) = n mod (b - 2)"
proof-
  from alpha_linear have S1: "\<alpha> (nat 2) n = n" by simp
  define q where "q = b - (nat 2)"
  from q_def assms le_mod_geq have S4: "b mod q = 2 mod q" by auto
  from assms S4 congruence have SN: "(\<alpha> b n) mod q = (\<alpha> 2 n) mod q" by blast
  from S1 SN q_def zmod_int show ?thesis by simp
qed

lemma congruence_jpos:
  fixes b m j l :: nat
  assumes "b>2" and "2*l*m+j>0"
  defines "n \<equiv> 2*l*m+j"
  shows "A b n = mat_mul (mat_pow l (mat_pow 2 (A b m))) (A b j)"
proof-
  from A_pow assms(1) have Abm2: "A b n = mat_pow n (B b)" by simp
  from Abm2 n_def have Bn: "mat_pow n (B b) =mat_pow (2*l*m+j) (B b)" by simp
  from mat_exp_law have as1: "mat_pow (2*l*m+j) (B b) = mat_mul (mat_pow l (mat_pow m (mat_pow 2 (B b)))) (mat_pow (j) (B b))"
    by (metis (no_types, lifting) mat_exp_law_mult mult.commute)
  from A_pow assms(1) B.elims mult.commute mat_exp_law_mult have as2: "mat_mul (mat_pow l (mat_pow m (mat_pow 2 (B b)))) (mat_pow (j) (B b))
    = mat_mul (mat_pow l (mat_pow 2 (A b m))) (A b j)" by metis
  from as2 as1 Abm2 Bn show ?thesis by auto
qed


lemma congruence_inverse: "b>2 \<Longrightarrow> mat_pow (n+1) (B_inv b) = A_inv b (n+1)"
  apply (induction n, simp add: B_inv.simps, auto) by (auto simp add: B_inv.simps)

lemma congruence_inverse2:
  fixes n b :: nat
  assumes "b>2"
  shows "mat_mul (mat_pow n (B b)) (mat_pow n (B_inv b)) = mat 1 0 0 1"
proof(induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have S1: "mat_pow (Suc(n)) (B b) = mat_mul (B b) (mat_pow n (B b))" by simp
  have S2: "mat_pow (Suc(n)) (B_inv b) = mat_mul (mat_pow n (B_inv b)) (B_inv b)"
    proof -
    have "\<forall>i ia ib ic. mat_pow 1 (mat ic ib ia i) = mat ic ib ia i"
      by simp
    hence "\<forall>m ma mb. mat_pow 1 m = m \<or> mat_mul mb m \<noteq> ma" by (metis mat2.exhaust)
    thus ?thesis
      by (metis (no_types) One_nat_def add_Suc_right diff_Suc_Suc diff_zero mat_exp_law mat_pow.simps(1) mat_pow.simps(2))
  qed
  define "C" where "C= (B b)"
  define "D" where "D = mat_pow n C"
  define "E" where "E = B_inv b"
  define "F" where "F = mat_pow n E"
  from S1 S2 C_def D_def E_def F_def have S3: "mat_mul (mat_pow (Suc(n)) C) (mat_pow (Suc(n)) E) = mat_mul (mat_mul C D) (mat_mul F E)" by simp
  from S3 mat_associativity mat2.exhaust C_def D_def E_def F_def have S4: "mat_mul (mat_pow (Suc(n)) C) (mat_pow (Suc(n)) E)
    = mat_mul C (mat_mul (mat_mul D F) E)" by metis
  from S4 Suc.hyps mat_neutral_element C_def D_def E_def F_def have S5: "mat_mul (mat_pow (Suc(n)) C) (mat_pow (Suc(n)) E) = mat_mul C E" by simp
  from S5 C_def E_def show ?case using B_inverse ID_def by auto
qed

lemma congruence_mult:
  fixes m :: nat
  assumes "b>2"
  shows "n>m ==> mat_pow (nat(int n- int m)) (B b) = mat_mul (mat_pow n (B b)) (mat_pow m (B_inv b))"
proof(induction n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  consider (eqm) "n == m" | (gm) "n < m" | (lm) "n>m" by linarith
  thus ?case
  proof cases
    case gm
    from Suc.prems gm not_less_eq show ?thesis by simp
  next case lm
    have S1: "mat_pow (nat(int (Suc(n)) - int m)) (B b) = mat_mul (B b) (mat_pow (nat(int n - int m)) (B b))"
      by (metis Suc.prems Suc_diff_Suc diff_Suc_1 diff_Suc_Suc mat_pow.simps(2) nat_minus_as_int)
    from lm S1 Suc.IH have S2: "mat_pow (nat(int (Suc(n)) - int m)) (B b) = mat_mul (B b) (mat_mul (mat_pow n (B b)) (mat_pow m (B_inv b)))" by simp
    from S2 mat_associativity mat2.exhaust have S3: "mat_pow (nat(int (Suc(n)) - int m)) (B b) = mat_mul (mat_mul (B b) (mat_pow n (B b))) (mat_pow m (B_inv b))" by metis
    from S3 show ?thesis by simp
  next case eqm
    from eqm have S1: "nat(int (Suc(n))- int m) = 1" by auto
    from S1 have S2: "mat_pow (nat(int (Suc(n))- int m)) (B b) == B b" by simp
    from eqm have S3: "(mat_pow (Suc(n)) (B b)) = mat_mul (B b) (mat_pow m (B b))" by simp
    from S3 have S35: "mat_mul (mat_pow (Suc(n)) (B b)) (mat_pow m (B_inv b)) = mat_mul (mat_mul (B b) (mat_pow m (B b))) (mat_pow m (B_inv b))" by simp
    from mat2.exhaust S35 mat_associativity have S4: "mat_mul (mat_pow (Suc(n)) (B b)) (mat_pow m (B_inv b))
      = mat_mul (B b) (mat_mul (mat_pow m (B b)) (mat_pow m (B_inv b)))" by smt
    from congruence_inverse2 assms have S5: "mat_mul (mat_pow m (B b)) (mat_pow m (B_inv b)) =  mat 1 0 0 1" by simp
    have S6: "mat_mul (B b) (B_inv b) = mat 1 0 0 1" using ID_def B_inverse by auto
    from S5 S6 eqm have S7: "mat_mul (mat_pow n (B b)) (mat_pow m (B_inv b)) = mat 1 0 0 1" by metis
    from S7 have S8: "mat_mul (B b) (mat_mul (mat_pow n (B b)) (mat_pow m (B_inv b))) == B b" by simp
    from eqm S2 S4 S8 show ?thesis by simp
  qed
qed

lemma congruence_jneg:
  fixes b m j l :: nat
  assumes "b>2" and "2*l*m > j" and "j>=1"
  defines "n \<equiv> nat(int 2*l*m- int j)"
  shows "A b n = mat_mul (mat_pow l (mat_pow 2 (A b m))) (A_inv b j)"
proof-
  from A_pow assms(1) have Abm2: "A b n = mat_pow n (B b)" by simp
  from Abm2 n_def have Bn: "A b n = mat_pow (nat(int 2*l*m- int j)) (B b)" by simp
  from Bn congruence_mult assms(1) assms(2) have Bn2: "A b n = mat_mul (mat_pow (2*l*m) (B b)) (mat_pow j (B_inv b))" by fastforce
  from assms(1) assms(3) congruence_inverse Bn2 add.commute le_Suc_ex have Bn3: "A b n = mat_mul (mat_pow (2*l*m) (B b)) (A_inv b j)" by smt
  from Bn3 A_pow assms(1) mult.commute B.simps mat_exp_law_mult have as3: "A b n = mat_mul (mat_pow l (mat_pow 2 (A b m))) (A_inv b j)" by metis
  from as3 A_pow add.commute assms(1) mat_exp_law mat_exp_law_mult show ?thesis by simp
qed

lemma matrix_congruence:
  fixes Y Z :: mat2
  fixes b m j l :: nat
  assumes "b>2"
  defines "X \<equiv> mat_mul Y Z"
  defines "a \<equiv> mat_11 Y" and "b0\<equiv> mat_12 Y" and "c \<equiv> mat_21 Y" and "d \<equiv> mat_22 Y"
  defines "e \<equiv> mat_11 Z" and "f \<equiv> mat_12 Z" and "g \<equiv> mat_21 Z" and "h \<equiv> mat_22 Z"
  defines "v \<equiv> \<alpha> b (m+1) - \<alpha> b (m-1)"
  assumes "a mod v = a1 mod v" and "b0 mod v = b1 mod v" and "c mod v = c1 mod v" and "d mod v = d1 mod v"
  shows "mat_21 X mod v = (c1*e+d1*g) mod v \<and> mat_22 X mod v = (c1*f+ d1*h) mod v" (is "?P \<and> ?Q")
proof -
  (* proof of ?P *)
  from X_def mat2.exhaust_sel c_def e_def d_def g_def have P1: "mat_21 X = (c*e+d*g)" 
    using mat2.sel by auto
  from assms(14) mod_mult_cong have P2: "(c*e) mod v = (c1*e) mod v" by blast
  from assms(15) mod_mult_cong have P3: "(d*g) mod v = (d1*g) mod v" by blast
  from P2 P3  mod_add_cong have P4: "(c*e+d*g) mod v = (c1*e+d1*g) mod v" by blast
  from P1 P4 have F1: ?P by simp
  (* proof of ?Q *)
  from X_def mat2.exhaust_sel c_def f_def d_def h_def mat2.sel(4) mat_mul.simps 
  have Q1: "mat_22 X = (c*f+d*h)" by metis
  from assms(14) mod_mult_cong have Q2: "(c*f) mod v = (c1*f) mod v" by blast
  from assms(15) mod_mult_cong have Q3: "(d*h) mod v = (d1*h) mod v" by blast
  from Q1 Q2 Q3 mod_add_cong have F2: ?Q by fastforce
  from F1 F2 show ?thesis by auto
qed

text \<open>3.38\<close>
lemma congruence_Abm:
  fixes b m n :: nat
  assumes "b>2"
  defines "v \<equiv> \<alpha> b (m+1) - \<alpha> b (m-1)"
  shows "(mat_21 (mat_pow n (mat_pow 2 (A b m))) mod v = 0 mod v)
  \<and> (mat_22 (mat_pow n (mat_pow 2 (A b m))) mod v = ((-1)^n) mod v)" (is "?P n \<and> ?Q n")
proof(induct n)
case 0
  from mat2.exhaust have S1: "mat_pow 0 (mat_pow 2 (A b m)) =  mat 1 0 0 1" by simp
  thus ?case by simp
next
  case (Suc n)
  define Z where "Z = mat_pow 2 (A b m)"
  define Y where "Y = mat_pow n Z"
  define X where "X = mat_mul Y Z"
  define c where "c = mat_21 Y"
  define d where "d = mat_22 Y"
  define e where "e = mat_11 Z"
  define f where "f = mat_12 Z"
  define g where "g = mat_21 Z"
  define h where "h = mat_22 Z"
  define d1 where "d1 = (-1)^n mod v"
  from d_def d1_def Z_def Y_def Suc.hyps have S1: "d mod v = d1 mod v" by simp
  from matrix_congruence assms(1) X_def v_def c_def d_def e_def d1_def g_def S1 
  have S2: "mat_21 X mod v = (c*e+d1*g) mod v" by blast
  from Z_def Y_def c_def Suc.hyps have S3: "c mod v = 0 mod v" by simp
  consider (eq0) "m = 0" | (g0) "m>0" by blast
  hence S4: "g mod v = 0"
  proof cases
    case eq0
    from eq0 have S1: "A b m = mat 1 0 0 1" using A.simps by simp
    from S1 Z_def div_3252 g_def show ?thesis by simp
    next
    case g0
    from g0 A.elims neq0_conv 
    have S1: "A b m = mat (\<alpha> b (m + 1)) (-(\<alpha> b m)) (\<alpha> b m) (-(\<alpha> b (m - 1)))" by metis
    from S1 assms(1) mat2.sel(3) mat_mul.simps mat_pow.simps
    have S2: "mat_21 (mat_pow 2 (A b m)) = (\<alpha> b m)*(\<alpha> b (m+1)) + (-\<alpha> b (m-1))*(\<alpha> b m)"
      by (auto)
    from S2 g_def Z_def g0 A.elims neq0_conv 
    have S3: "g = (\<alpha> b (m+1))*(\<alpha> b m)- (\<alpha> b m)*(\<alpha> b (m-1))" by simp
    from S3 g_def v_def mod_mult_self1_is_0 mult.commute right_diff_distrib show ?thesis by metis
  qed
  from S2 S3 S4 Z_def div_3252 g_def mat2.exhaust_sel mod_0 have F1: "?P (Suc(n))" by metis
  (* Now proof of Q *)
  from d_def d1_def Z_def Y_def Suc.hyps have Q1: "d mod v = d1 mod v" by simp
  from matrix_congruence assms(1) X_def v_def c_def d_def f_def d1_def h_def S1 
  have Q2: "mat_22 X mod v = (c*f+d1*h) mod v" by blast
  from Z_def Y_def c_def Suc.hyps have Q3: "c mod v = 0 mod v" by simp
  consider (eq0) "m = 0" | (g0) "m>0" by blast
  hence Q4: "h mod v = (-1) mod v"
  proof cases
    case eq0
    from eq0 have S1: "A b m = mat 1 0 0 1" using A.simps by simp
    from eq0 v_def have S2: "v = 1" by simp
    from S1 S2 show ?thesis by simp
    next
    case g0
    from g0 A.elims neq0_conv have S1: "A b m = mat (\<alpha> b (m + 1)) (-(\<alpha> b m)) (\<alpha> b m) (-(\<alpha> b (m - 1)))" by metis
    from S1 A_pow assms(1) mat2.sel(4) mat_exp_law mat_exp_law_mult mat_mul.simps mult_2
    have S2: "mat_22 (mat_pow 2 (A b m)) = (\<alpha> b m)*(-(\<alpha> b m)) + (-(\<alpha> b (m - 1)))*(-(\<alpha> b (m - 1)))" 
      by auto
    from S2 Z_def h_def have S3: "h = -(\<alpha> b m)*(\<alpha> b m) + (\<alpha> b (m - 1))*(\<alpha> b (m - 1))" by simp
    from v_def add.commute diff_add_cancel mod_add_self2 have S4: "(\<alpha> b (m - 1)) mod v = \<alpha> b (m+1) mod v" by metis
    from S3 S4 mod_diff_cong mod_mult_left_eq mult.commute mult_minus_right uminus_add_conv_diff
      have S5: "h mod v = (-(\<alpha> b m)*(\<alpha> b m) + (\<alpha> b (m - 1))*(\<alpha> b (m + 1))) mod v" by metis
      from One_nat_def add.right_neutral add_Suc_right \<alpha>.elims diff_Suc_1 g0 le_imp_less_Suc le_simps(1) neq0_conv Suc_diff_1 alpha_n
    have S6: "\<alpha> b (m + 1) = b* (\<alpha> b m)- \<alpha> b (m-1)"
      by (smt Suc_eq_plus1 Suc_pred' \<alpha>.elims alpha_superlinear assms(1) g0 nat.inject of_nat_0_less_iff of_nat_1 of_nat_add)
    from S6 have S7: "(\<alpha> b (m - 1))*(\<alpha> b (m + 1)) = (int b) * (\<alpha> b (m-1) * (\<alpha> b m)) - (\<alpha> b (m-1))^2"
    proof -
      have f1: "\<forall>i ia. - ((ia::int) * i) = ia * - i" by simp
      have "\<forall>i ia ib ic. (ic::int) * (ib * ia) + ib * i = ib * (ic * ia + i)" by (simp add: distrib_left)
      thus ?thesis using f1 by (metis S6 ab_group_add_class.ab_diff_conv_add_uminus power2_eq_square)
    qed
    from S7 have S8: "(-(\<alpha> b m)*(\<alpha> b m) + (\<alpha> b (m - 1))*(\<alpha> b (m + 1)))
      = -1*(\<alpha> b (m-1))^2 + (int b) * (\<alpha> b (m-1) * (\<alpha> b m)) - (\<alpha> b m)^2" by (simp add: power2_eq_square)
    from alpha_det2  assms(1) g0 have S9: "-1*(\<alpha> b (m-1))^2 + (int b) * (\<alpha> b (m-1) * (\<alpha> b m)) - (\<alpha> b m)^2 = -1" by smt
    from S5 S8 S9 show ?thesis by simp
  qed
  from Q2 Q3 Q4 Suc_eq_plus1 add.commute add.right_neutral d1_def mod_add_right_eq mod_mult_left_eq mod_mult_right_eq mult.right_neutral
    mult_minus1 mult_minus_right mult_zero_left power_Suc have Q5: "mat_22 X mod v = (-1)^(n+1) mod v" by metis
  from Q5 Suc_eq_plus1 X_def Y_def Z_def mat_exp_law mat_exp_law_mult mult.commute mult_2 one_add_one have F2: "?Q (Suc(n))" by metis
  from F1 F2 show ?case by blast
qed

text \<open> 3.36 requires two lemmas 361 and 362 \<close>

lemma 361:
  fixes b m j l :: nat
  assumes "b>2"
  defines "n \<equiv> 2*l*m + j"
  defines "v \<equiv> \<alpha> b (m+1) - \<alpha> b (m-1)"
  shows "(\<alpha> b n) mod v = ((-1)^l * \<alpha> b j) mod v"
proof -
  define Y where "Y = mat_pow l (mat_pow 2 (A b m))"
  define Z where "Z = A b j"
  define X where "X = mat_mul Y Z"
  define c where "c = mat_21 Y"
  define d where "d = mat_22 Y"
  define e where "e = mat_11 Z"
  define g where "g = mat_21 Z"
  define d1 where "d1 = (-1)^l mod v"
  from congruence_Abm assms(1) d_def v_def Y_def d1_def have S0: "d mod v = d1 mod v" by simp_all
  from matrix_congruence assms(1) X_def v_def c_def d_def e_def d1_def g_def S0 have S1: "mat_21 X mod v = (c*e+d1*g) mod v" by blast
  from congruence_Abm d1_def v_def mod_mod_trivial have S2: "d1 mod v = (-1)^l mod v" by blast
  from congruence_Abm Y_def assms(1) c_def v_def have S3: "c mod v = 0" by simp
  from Z_def g_def A.elims \<alpha>.simps(1) mat2.sel(3) mat2.exhaust have S4: "g = \<alpha> b j" by metis
  from A_pow assms(1) mat_exp_law mat_exp_law_mult mult_2 mult_2_right n_def X_def Y_def Z_def have S5: "A b n = X" by metis
  from S5 A.elims \<alpha>.simps(1) mat2.sel(3) Z_def Y_def have S6: "mat_21 X = \<alpha> b n" by metis
  from S2 S3 S4 S6 S1 add.commute mod_0 mod_mult_left_eq mod_mult_self2 mult_zero_left zmod_eq_0_iff show ?thesis by metis
qed

lemma 362:
fixes b m j l :: nat
  assumes "b>2" and "2*l*m > j" and "j>=1"
  defines "n \<equiv> 2*l*m - j"
  defines "v \<equiv> \<alpha> b (m+1) - \<alpha> b (m-1)"
  shows "(\<alpha> b n) mod v = -((-1)^l * \<alpha> b j) mod v"
proof -
  define Y where "Y = mat_pow l (mat_pow 2 (A b m))"
  define Z where "Z = A_inv b j"
  define X where "X = mat_mul Y Z"
  define c where "c = mat_21 Y"
  define d where "d = mat_22 Y"
  define e where "e = mat_11 Z"
  define g where "g = mat_21 Z"
  define d1 where "d1 = (-1)^l mod v"
  from congruence_Abm assms(1) d_def v_def Y_def d1_def have S0: "d mod v = d1 mod v" by simp_all
  from matrix_congruence assms(1) X_def v_def c_def d_def e_def d1_def g_def S0 have S1: "mat_21 X mod v = (c*e+d1*g) mod v" by blast
  from congruence_Abm d1_def v_def mod_mod_trivial have S2: "d1 mod v = (-1)^l mod v" by blast
  from congruence_Abm Y_def assms(1) c_def v_def have S3: "c mod v = 0" by simp
  from Z_def g_def have S4: "g = - \<alpha> b j" by simp
  from congruence_jneg assms(1) assms(2) assms(3) n_def X_def Y_def Z_def have S5: "A b n = X" by (simp add: nat_minus_as_int)
  from S5 A.elims \<alpha>.simps(1) mat2.sel(3) Z_def Y_def have S6: "mat_21 X = \<alpha> b n" by metis
  from S2 S3 S4 S6 S1 add.commute mod_0 mod_mult_left_eq mod_mult_self2 mult_minus_right mult_zero_left zmod_eq_0_iff show ?thesis by metis
qed

text \<open>Equation 3.36\<close>
lemma 36:
fixes b m j l :: nat
  assumes "b>2"
  assumes "(n = 2 * l * m + j \<or> (n = 2 * l * m - j \<and> 2 * l * m > j  \<and> j \<ge> 1)) "
  defines "v \<equiv> \<alpha> b (m+1) - \<alpha> b (m-1)"
  shows  "(\<alpha> b n) mod v = \<alpha> b j mod v \<or> (\<alpha> b n) mod v = -\<alpha> b j mod v" using assms(2)
  apply(auto)  
  subgoal using 361 assms(1) v_def
    apply(cases "even l" ) 
    by simp+
  subgoal using 362 assms(1) v_def
    apply(cases "even l" ) 
    by simp+
  done

subsubsection \<open>Diophantine definition of a sequence alpha\<close>
definition alpha_equations :: "nat \<Rightarrow> nat \<Rightarrow> nat 
                            \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "alpha_equations a b c  r s t u v w x y = (
  \<comment> \<open>3.41\<close> b > 3 \<and>
  \<comment> \<open>3.42\<close> u^2 + t ^ 2 = 1 + b * u * t \<and> 
  \<comment> \<open>3.43\<close> s^2 + r ^ 2 = 1 + b * s * r \<and>
  \<comment> \<open>3.44\<close> r < s \<and>
  \<comment> \<open>3.45\<close> u ^ 2 dvd s \<and>
  \<comment> \<open>3.46\<close> v + 2 * r = (b) * s \<and>
  \<comment> \<open>3.47\<close> w mod v = b mod v \<and>
  \<comment> \<open>3.48\<close> w mod u = 2 mod u \<and>
  \<comment> \<open>3.49\<close> 2 < w \<and>
  \<comment> \<open>3.50\<close> x ^ 2 + y ^ 2 = 1 +  w * x * y \<and>
  \<comment> \<open>3.51\<close> 2 * a < u \<and>
  \<comment> \<open>3.52\<close> 2 * a < v \<and>
  \<comment> \<open>3.53\<close> a mod v = x mod v \<and>
  \<comment> \<open>3.54\<close> 2 * c < u \<and>
  \<comment> \<open>3.55\<close> c mod u = x mod u)"

text \<open>The sufficiency\<close>
lemma alpha_equiv_suff:
  fixes a b c::nat
  assumes "\<exists>r s t u v w x y. alpha_equations a b c r s t u v w x y"
  shows "3 < b \<and> int a = (\<alpha> b c)"
proof -
  from assms obtain r s t u v w x y where eq: "alpha_equations a b c r s t u v w x y" by auto
  have 41: "b > 3"                           using alpha_equations_def eq by auto
  have 42: "u^2  + t ^ 2 = 1 +b * u * t"     using alpha_equations_def eq by auto 
  have 43: "s^2 + r ^ 2 = 1 + b * s * r"     using alpha_equations_def eq by auto
  have 44: "r < s"                           using alpha_equations_def eq by auto
  have 45: "u ^ 2 dvd s"                     using alpha_equations_def eq by auto
  have 46: "v + 2 * r = b * s"               using alpha_equations_def eq by auto
  have 47: "w mod v =  b mod v"              using alpha_equations_def eq by auto
  have 48: "w mod u = 2 mod u"               using alpha_equations_def eq by auto
  have 49: "2 < w"                           using alpha_equations_def eq by auto
  have 50: "x ^ 2  + y ^ 2 = 1 + w * x * y"  using alpha_equations_def eq by auto
  have 51: "2 * a < u"                       using alpha_equations_def eq by auto
  have 52: "2 * a < v"                       using alpha_equations_def eq by auto
  have 53: "a mod v = x mod v"               using alpha_equations_def eq by auto
  have 54: "2 * c < u"                       using alpha_equations_def eq by auto
  have 55: "int c mod u = x mod u"           using alpha_equations_def eq by auto

  have "b > 2" using \<open>b>3\<close> by auto
  have "u > 0" using 51 by auto

  (* These first three equations are all proved very similarly. *)
  text \<open>Equation 3.56\<close>
  have "\<exists>k. u = \<alpha> b k" using 42 alpha_char_eq2 by (simp add: \<open>2 < b\<close> power2_eq_square)
  then obtain k where 56: "u = \<alpha> b k" by auto

  text \<open>Equation 3.57\<close>
  have "\<exists>m. s = \<alpha> b m \<and> r = \<alpha> b (m-1)" using 43 44 alpha_char_eq[of r s b] diff_Suc_1
    by (metis power2_eq_square)
  then obtain m where 57: "s = \<alpha> b m \<and> r = \<alpha> b (m-1)" by auto
 
 (* These are some properties we need multiple times *)
  have m_pos: "m \<noteq> 0" using "44" "57" not_less_eq by fastforce
  have alpha_pos: "\<alpha> b m > 0" using "44" "57" by linarith


  text \<open>Equation 3.58\<close>
  have "\<exists>n. x = \<alpha> w n" using 50 alpha_char_eq2 by (simp add: "49" power2_eq_square)
  then obtain n where 58: "x = \<alpha> w n" by auto

  text \<open>Equation 3.59\<close>
  have "\<exists>l j. (n = 2 * l * m + j \<or> n = 2 * l * m - j \<and> 2 * l * m > j \<and> j \<ge> 1) \<and> j \<le> m"
 proof -
    define q where "q = n mod m"
    obtain p where p_def: "n = p * m + q" using mod_div_decomp q_def by auto
    have q1: "q \<le> m" using 44 57
      by (metis diff_le_self le_0_eq le_simps(1) linorder_not_le mod_less_divisor nat_int q_def)
    consider (c1) "even p" | (c2) "odd p" by auto
    thus ?thesis
    proof(cases)
      case c1
      thus ?thesis using p_def q1 by blast
    next
      case c2
      obtain d where "p=2*d+1" using c2 oddE by blast
      define l where "l=d+1"
      hence jpt: "l>0" by simp
      from \<open>p=2*d+1\<close> l_def have c21: "p=2*l-1" by auto
      have c22: "n=2*l*m-(m-q)"
        by (metis Nat.add_diff_assoc2 add.commute c21 diff_diff_cancel diff_le_self jpt mult_eq_if
            mult_is_0 neq0_conv p_def q1 zero_neq_numeral)
      thus ?thesis using diff_le_self
        by (metis add.left_neutral diff_add_inverse2 diff_zero less_imp_diff_less mult.right_neutral 
            mult_eq_if mult_zero_right not_less zero_less_diff)
    qed
  qed

  (* here we add some conditions that are implicit in the proof but necessary for Isabelle *)
  then obtain l j where 59: " (n = 2 * l * m + j \<or> n = 2 * l * m - j \<and> 2 * l * m > j \<and> j \<ge> 1) \<and> j \<le> m" by auto

  text \<open>Equation 3.60\<close>
  have 60: "u dvd m" 
    using 45 56 57 divisibility_alpha2[of b m k] \<open>b>2\<close>
    by (metis dvd_trans dvd_triv_right int_dvd_int_iff m_pos neq0_conv of_nat_power)

  text \<open>Equation 3.61\<close>
  have 61: "v = \<alpha> b (m+1)- \<alpha> b (m-1)"
  proof-
    have "v = b*(\<alpha> b m) - 2*(\<alpha> b (m-1))" using 46 57 by (metis add_diff_cancel_right' mult_2 of_nat_add of_nat_mult)
    thus ?thesis using alpha_n[of b "m-1"] m_pos by auto
  qed

  text \<open>Equation 3.62.1\<close>
  have "a mod v = \<alpha> b n mod v" using 53 58 47 congruence[of w v b n] by (simp add: zmod_int)
  hence "a mod v = \<alpha> b j mod v \<or> a mod v = -\<alpha> b j mod v" using 36[of b] 61 59 \<open>2 < b\<close> by auto
  (* more usable version *)
  hence 62: "v dvd (a+ \<alpha> b j) \<or> v dvd (a - \<alpha> b j)" using mod_eq_dvd_iff zmod_int by auto
  
  text \<open>Equation 3.63\<close>
  (* This could be rewritten in a single proof if none of the 631-634 are reused *)
  
  have 631: "2*\<alpha> b j \<le> 2* \<alpha> b m" using 59 alpha_strictly_increasing_general[of b j m] \<open>2 < b\<close> by force
  
  have "b - 2 \<ge> 2" using 41 by simp
  moreover have "\<alpha> b m > 0" using "44" "57" by linarith
  ultimately have 632: "2 * \<alpha> b m \<le> (b - 2) * \<alpha> b m" by auto

  have "(b - 2) * \<alpha> b m = b * \<alpha> b m - 2*  \<alpha> b m" using  \<open>2 < b\<close>
    by (simp add: int_distrib(4) mult.commute of_nat_diff)
  moreover have "b * \<alpha> b m - 2*  \<alpha> b m  < b * \<alpha> b m - 2 * \<alpha> b (m - 1)" using "44" "57" by linarith
  ultimately have 633: "(b - 2) * \<alpha> b m < b * \<alpha> b m - 2 * \<alpha> b (m - 1)" by auto

  have 634: " b * \<alpha> b m - 2 * \<alpha> b (m - 1) = v" using 61 alpha_n[of b "m-1"] m_pos by simp

  have 63: "2*\<alpha> b j < v" using 631 632 633 634 by auto

  text \<open>Equation 3.64\<close>

  hence 64: "a = \<alpha> b j"
  proof(cases "0 < a + \<alpha> b j")
    case True
    moreover have "a + \<alpha> b j < v" using 52 63 by linarith
    ultimately show ?thesis using 62
      apply auto
      subgoal using zdvd_not_zless by blast
      subgoal
        by (smt \<open>2 < b\<close> alpha_superlinear dvd_add_triv_left_iff negative_zle zdvd_not_zless)
      done
    next
      case False
      hence "j = 0" using \<open>2 < b\<close> alpha_strictly_increasing_general by force
      thus ?thesis using False by auto
  qed


  text \<open>Equation 3.65\<close>
  have 65: "c mod u = n mod u"
  proof -
    have "c mod u = \<alpha> w n mod u" using 55 58 zmod_int by (simp add: )
    moreover have "... = n mod u" using 48 alpha_linear congruence zmod_int by presburger
    ultimately show ?thesis by linarith
  qed

  text \<open>Equation 3.66\<close>
  have "2 * j \<le> 2 * \<alpha> b j \<and> 2 * a < u" 
    using 51 alpha_superlinear \<open>b>2\<close> by auto
  hence 66: "2*j < u" using "64" by linarith

  text \<open>Equation 3.67\<close>
  have 652: "u dvd (n+j) \<or> u dvd (n-j)" using 60 59 by auto

  hence "c = j" using 66 54
  proof-
     have "c + j < u" using 66 54 by linarith
     thus ?thesis using 652
      apply auto
      subgoal
        by (metis "65" add_cancel_right_right dvd_eq_mod_eq_0 mod_add_left_eq mod_if not_add_less2 not_gr_zero)
      subgoal
        by (metis "59" "60" "65" "66" Nat.add_diff_assoc2 \<open>\<lbrakk>c + j < u; u dvd n + j\<rbrakk> \<Longrightarrow> c = j\<close> 
            add_diff_cancel_right' add_lessD1 dvd_mult le_add2 le_less mod_less mod_nat_eqI mult_2)
      done
  qed

  show ?thesis using \<open>b>3\<close> 64 \<open>c=j\<close> by auto
qed


text \<open> 3.7.2 The necessity \<close>

lemma add_mod:
  fixes p q :: int
  assumes "p mod 2 = 0" "q mod 2 = 0"
  shows "(p+q) mod 2 = 0 \<and> (p-q) mod 2 = 0"
  using assms(1) assms(2) by auto

lemma one_odd:
  fixes b n :: nat
  assumes "b>2"
  shows "(\<alpha> b n) mod 2 = 1 \<or> (\<alpha> b (n+1)) mod 2 = 1"
proof(rule ccontr)
  assume asm: "\<not>(\<alpha> b n mod 2 = 1 \<or> \<alpha> b (n + 1) mod 2 = 1)"
  from asm have step1: "(\<alpha> b n mod 2 = 0 \<and> \<alpha> b (n + 1) mod 2 = 0)" by simp
  from step1 have s1: "(\<alpha> b n)^2 mod 2 = 0 \<and> (\<alpha> b (n+1))^2 mod 2 = 0" by auto
  from step1 have s2: "(int b)*(\<alpha> b n)*(\<alpha> b (n+1)) mod 2 = 0" by auto
  from s1 have s3: "((\<alpha> b (n+1))^2 + (\<alpha> b n)^2) mod 2 = 0" by auto
  from s2 s3 add_mod have s4: "((\<alpha> b (n+1))^2 + (\<alpha> b n)^2 - (int b)*((\<alpha> b n)*(\<alpha> b (n+1)))) mod 2 = 0"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3))
  have s5: "(\<alpha> b (n+1))^2+(\<alpha> b n)^2-(int b)*((\<alpha> b n)*(\<alpha> b (n+1)))=(\<alpha> b (n+1))^2-(int b)*(\<alpha> b (n+1)*(\<alpha> b n))+(\<alpha> b n)^2" by simp
  from s4 s5 have s6: "((\<alpha> b (n+1))^2-(int b)*(\<alpha> b (n+1)*(\<alpha> b n))+(\<alpha> b n)^2) mod 2 = 0"
  proof -
    have f1: "(\<alpha> b (n + 1))\<^sup>2 - int b * (\<alpha> b (n + 1) * \<alpha> b n) = (\<alpha> b (n + 1))\<^sup>2 + - 1 * (int b * (\<alpha> b (n + 1) * \<alpha> b n))"
      by simp
    have f2: "(\<alpha> b (n + 1))\<^sup>2 + - 1 * (int b * (\<alpha> b (n + 1) * \<alpha> b n)) + (\<alpha> b n)\<^sup>2 = (\<alpha> b (n + 1))\<^sup>2 + (\<alpha> b n)\<^sup>2 + - 1 * (int b * (\<alpha> b n * \<alpha> b (n + 1)))"
      by simp
    have "((\<alpha> b (n + 1))\<^sup>2 + (\<alpha> b n)\<^sup>2 + - 1 * (int b * (\<alpha> b n * \<alpha> b (n + 1)))) mod 2 = 0"
      using s4 by fastforce
    thus ?thesis using f2 f1 by presburger
  qed
  from s6 alpha_det1 show False by (simp add: assms mult.assoc)
qed

lemma oneodd:
  fixes b n :: nat
  assumes "b>2"
  shows "odd (\<alpha> b n) = True \<or> odd (\<alpha> b (n+1)) = True"
  using assms odd_iff_mod_2_eq_one one_odd by auto

lemma cong_solve_nat: "a \<noteq> 0 \<Longrightarrow> \<exists>x. (a*x) mod n = (gcd a n) mod n"
  for a n :: nat
  apply (cases "n=0")
    apply auto
  apply (insert bezout_nat [of a n], auto)
  by (metis mod_mult_self4)

lemma cong_solve_coprime_nat: "coprime (a::nat) (n::nat) \<Longrightarrow> \<exists>x. (a*x) mod n = 1 mod n"
  using cong_solve_nat[of a n] coprime_iff_gcd_eq_1[of a n] by fastforce

lemma chinese_remainder_aux_nat:
  fixes m1 m2 :: nat
  assumes a:"coprime m1 m2"
  shows "\<exists>b1 b2. b1 mod m1 = 1 mod m1 \<and> b1 mod m2 = 0 mod m2 \<and> b2 mod m1 = 0 mod m1 \<and> b2 mod m2 = 1 mod m2"
proof -
  from cong_solve_coprime_nat [OF a] obtain x1 where 1: "(m1*x1) mod m2 = 1 mod m2" by auto
  from a have b: "coprime m2 m1"
    by (simp add: coprime_commute)
  from cong_solve_coprime_nat [OF b] obtain x2 where 2: "(m2*x2) mod m1 = 1 mod m1" by auto
  have "(m1*x1) mod m1 = 0" by simp
  have "(m2*x2) mod m2 = 0" by simp
  show ?thesis using 1 2
    by (metis mod_0 mod_mult_self1_is_0)
qed

lemma cong_scalar2_nat: "a mod m = b mod m \<Longrightarrow> (k*a) mod m = (k*b) mod m"
  for a b k :: nat
  by (rule mod_mult_cong) simp_all

lemma chinese_remainder_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
  shows "\<exists>x. x mod m1 = u1 mod m1 \<and> x mod m2 = u2 mod m2"
proof -
  from chinese_remainder_aux_nat [OF a] obtain b1 b2 where "b1 mod m1 = 1 mod m1" and "b1 mod m2 = 0 mod m2" and
"b2 mod m1 = 0 mod m1" and "b2 mod m2 = 1 mod m2" by force
  let ?x = "u1*b1+u2*b2"
  have "?x mod m1 = (u1*1+u2*0) mod m1"
    apply (rule mod_add_cong)
     apply(rule cong_scalar2_nat)
     apply (rule \<open>b1 mod m1 = 1 mod m1\<close>)
    apply(rule cong_scalar2_nat)
    apply (rule \<open>b2 mod m1 = 0 mod m1\<close>)
    done
  hence 1:"?x mod m1 = u1 mod m1" by simp
  have "?x mod m2 = (u1*0+u2*1) mod m2"
    apply (rule mod_add_cong)
     apply(rule cong_scalar2_nat)
     apply (rule \<open>b1 mod m2 = 0 mod m2\<close>)
    apply(rule cong_scalar2_nat)
    apply (rule \<open>b2 mod m2 = 1 mod m2\<close>)
    done
  hence "?x mod m2 = u2 mod m2" by simp
  with 1 show ?thesis by  blast
qed

lemma nat_int1: "\<forall>(w::nat) (u::int).u>0 \<Longrightarrow> (w mod nat u = 2 mod nat u \<Longrightarrow> int w mod u = 2 mod u)"
  by blast

lemma nat_int2: "\<forall>(w::nat) (b::nat) (v::int).u>0 \<Longrightarrow> (w mod nat v = b mod nat v \<Longrightarrow> int w mod v = int b mod v)"
  by (metis mod_by_0 nat_eq_iff zmod_int)

lemma lem:
  fixes u t::int and b::nat
  assumes "u^2-int b*u*t+t^2=1" "u\<ge>0" "t\<ge>0"
  shows "(nat u)^2+(nat t)^2=1+b*(nat u)*(nat t)"
proof -
  define U where "U=nat u"
  define T where "T=nat t"
  from U_def T_def assms have UT: "int U=u \<and> int T = t" using int_eq_iff by blast
  from UT have UT1: "int (b*U*T) = b*u*t" by simp
  from UT have UT2: "int (U^2+T^2)=u^2+t^2" by simp
  from UT2 assms have sth: "int (U^2+T^2)\<ge>b*u*t" by auto
  from sth assms have sth1: "U^2+T^2\<ge>b*U*T" using UT1 by linarith
  from sth1 of_nat_diff have sth2: "int (U^2+T^2-b*U*T) = int (U^2+T^2) - int (b*U*T)" by blast
  from UT1 UT2 have UT3: "int (U^2+T^2)-int (b*U*T)=u^2+t^2-b*u*t" by simp
  from sth2 UT3 assms have sth4: "int (U^2+T^2-b*U*T) = 1" by auto
  from sth4 have sth5: "U^2+T^2-b*U*T=1" by simp
  from sth5 have sth6: "U^2+T^2=1+b*U*T" by simp
  show ?thesis using sth6 U_def T_def by simp
qed

text \<open>The necessity\<close>

lemma alpha_equiv_nec: 
  "b > 3 \<and> a = \<alpha> b c \<Longrightarrow> \<exists>r s t u v w x y. alpha_equations a b c r s t u v w x y"
proof -
  assume assms: "b > 3 \<and> a = \<alpha> b c"
  have s1: "\<exists>(k::nat) (u::int) (t::int).u=\<alpha> b k \<and> odd u = True \<and> 2*int a<u \<and> u<t \<and> u^2-(int b)*u*t+t^2=1 \<and> k>0 \<and> t = \<alpha> b (k+1)"
  proof -
    define j::nat where "j=2*(a)+1"
    have rd: "j>0" by (simp add: j_def)
    consider (c1) "odd (\<alpha> b j) = True" | (c2) "odd (\<alpha> b (j+1)) = True"
      using assms oneodd by fastforce
    thus ?thesis
    proof cases
      case c1
      define k::nat where "k=j"
      define u::int where "u=\<alpha> b k"
      define t::int where "t=\<alpha> b (k+1)"
      have stp: "k>0" by (simp add: k_def j_def)
      from alpha_strictly_increasing assms have abc: "u<t" by (simp add: u_def t_def)
      have c11: "odd u = True" by (simp add: c1 k_def u_def)
      from alpha_det1 u_def t_def alpha_det2 assms(1) have bcd: "u^2-(int b)*u*t+t^2=1"
        by (metis (no_types, lifting) One_nat_def Suc_1 Suc_less_eq add_diff_cancel_right'
                  add_gr_0 less_Suc_eq mult.assoc numeral_3_eq_3)
      have c12: "int k>2*a" by (simp add: k_def j_def)
      from alpha_superlinear c12 have c13: "2*a<u"
        by (smt add_lessD1 assms(1) numeral_Bit1 numeral_One one_add_one u_def)
      from c11 c13 k_def u_def t_def abc bcd stp show ?thesis by auto
    next
      case c2
      define k::nat where "k=j+1"
      define u::int where "u=\<alpha> b k"
      define t::int where "t=\<alpha> b (k+1)"
      have stc: "k>0" by (simp add: k_def j_def)
      from alpha_strictly_increasing assms have abc: "u<t" by (simp add: u_def t_def)
      from c2 k_def u_def have c21: "odd u = True" by auto
      from alpha_det1 u_def t_def alpha_det2 assms(1) have bcd: "u^2-(int b)*u*t+t^2=1"
        by (metis (no_types, lifting) One_nat_def Suc_1 Suc_less_eq add_diff_cancel_right'
                    add_gr_0 less_Suc_eq mult.assoc numeral_3_eq_3)
      have c22: "int k>2*a" by (simp add: k_def j_def)
      from alpha_superlinear c22 have c23: "2*a<u"
        by (smt add_lessD1 assms(1) numeral_Bit1 numeral_One one_add_one u_def)
      from c21 c23 abc bcd k_def u_def t_def show ?thesis by auto
    qed
  qed
  then obtain k u t where "u=\<alpha> b k \<and> odd u = True \<and> 2*int a<u \<and> u<t \<and> u^2-(int b)*u*t+t^2=1 \<and> k>0 \<and> t= \<alpha> b (k+1)" by force
  define m where "m=(nat u)*k"
  define s where "s=\<alpha> b m"
  define r where "r=\<alpha> b (m-1)"
  note udef = \<open>u = \<alpha> b k \<and> odd u = True \<and> 2 * int a < u \<and> u < t \<and> u\<^sup>2 - int b * u * t + t\<^sup>2 = 1 \<and> 0 < k \<and> t = \<alpha> b (k+1)\<close>
  from assms have s211: "int b > 3" by simp
  from assms alpha_superlinear have a354: "c\<le>a"
    by (simp add: nat_int_comparison(3))
  from a354 udef have 354: "2* int c<u" by simp
  from alpha_superlinear s211 m_def udef have rd: "\<alpha> b k \<ge> int k" by simp
  from alpha_strictly_increasing s211 s1 m_def s_def udef r_def have s212: "\<alpha> b (m-1) < \<alpha> b m"
    by (smt One_nat_def Suc_pred nat_0_less_mult_iff zero_less_nat_eq)
  from s212 r_def s_def have 344: "r<s" by simp
  from alpha_det2 assms s_def r_def m_def have s22: "r^2-int b*r*s+s^2=1" by (smt One_nat_def Suc_eq_plus1 udef add_lessD1
         alpha_superlinear mult.assoc nat_0_less_mult_iff numeral_3_eq_3 of_nat_0 of_nat_less_iff one_add_one zero_less_nat_eq)
  from s22 have 343: "s^2-int b*s*r+r^2=1" by algebra
  from m_def udef have xyz: "(int k)*(\<alpha> b k) dvd (int m) \<and> k dvd m" by simp
  from xyz divisibility_alpha2 have wxyz: "(\<alpha> b k)*(\<alpha> b k) dvd (\<alpha> b m)" by (smt assms dvd_mult_div_cancel int_nat_eq less_imp_le_nat m_def mult_pos_pos neq0_conv not_less not_less_eq numeral_2_eq_2 numeral_3_eq_3 of_nat_0_less_iff power2_eq_square udef)
  from wxyz udef s_def have 345: "u^2 dvd s" by (simp add: power2_eq_square)
  define v where "v = b*s-2*r"
  from v_def s_def r_def alpha_n have 370: "v = \<alpha> b (m+1) - \<alpha> b (m-1)"
    by (smt Suc_eq_plus1 add_diff_inverse_nat diff_Suc_1 neq0_conv not_less_eq s212 zero_less_diff)
  have 371: "v = b*\<alpha> b m - 2*\<alpha> b (m-1)" using v_def s_def r_def by simp
  from alpha_strictly_increasing assms m_def udef have asd: "\<alpha> b m > 0"
    by (smt Suc_pred nat_0_less_mult_iff s211 zero_less_nat_eq)
  from assms asd 371 have 372: "v\<ge>4*\<alpha> b m -2*\<alpha> b (m-1)" by simp
  from 372 assms have 373: "v>2*\<alpha> b m \<and> 4*\<alpha> b m -2*\<alpha> b (m-1) > 2*\<alpha> b m" using s212 by linarith
  from 373 assms alpha_superlinear have 374: "2*\<alpha> b m \<ge> 2*m \<and> v>2*m"
    by (smt One_nat_def Suc_eq_plus1 add_lessD1 distrib_right mult.left_neutral numeral_3_eq_3 of_nat_add one_add_one)
  from udef have pre1: "k\<ge>1 \<and> u\<ge>1" using rd by linarith
  from pre1 374 m_def have pre2: "m\<ge>u" by simp
  from pre2 374 have 375: "2*m\<ge>2*u \<and> v>2*u" by simp
  from 375 udef have 376: "2*u>2*a \<and> v>2*a" using pre1 by linarith
  have u_v_coprime: "coprime u v"
  proof -
    obtain d::nat where d: "d = gcd u v"
      by (metis gcd_int_def)
    from \<open>d = gcd u v\<close> have ddef: "d dvd u \<and> d dvd v" by simp
    from 345 ddef have stp1: "d dvd s" using dvd_mult_left dvd_trans s_def udef wxyz by blast
    from v_def stp1 ddef have stp2: "d dvd 2*r" by algebra
    from ddef udef have d_odd: "odd d" using dvd_trans by auto
    have r2even: "even (2*r)" by simp
    from stp2 d_odd r2even have stp3: "(2*d) dvd (2*r)" by fastforce
    from stp3 have stp4: "d dvd r" by simp
    from stp1 stp4 have stp5: "d dvd s^2 \<and> d dvd (-int b*s*r) \<and> d dvd r^2" by (simp add: power2_eq_square)
    from stp5 have stp6: "d dvd (s^2-int b*s*r+r^2)" by simp
    from 343 stp6 have stp7: "d dvd 1" by simp
    show ?thesis using stp7 d by auto
  qed
  have wdef: "\<exists>w::nat. int w mod u = 2 mod u \<and> int w mod v = int b mod v \<and> w>2"
  proof -
    from pre1 m_def have mg: "m\<ge>1" by auto
    from s_def r_def 344 have srg: "s-r\<ge>1" by simp
    from assms have bg: "b\<ge>4" by simp
    from bg have bsr: "((int b)*s-2*r)\<ge>(4*s-2*r)" using 372 r_def s_def v_def by blast
    have t1: "v\<ge>2+2*s" using bsr srg v_def by simp
    from s_def have sg: "s\<ge>1" using asd by linarith
    from sg t1 have t2: "v\<ge>4" by simp
    from u_v_coprime have u_v_coprime1:"coprime (nat u) (nat v)" using pre1 t2
      using coprime_int_iff by fastforce
    obtain z::nat where "z mod nat u = 2 mod nat u \<and> z mod nat v = b mod nat v" using chinese_remainder_nat u_v_coprime1 by force
    note zdef = \<open>z mod nat u = 2 mod nat u \<and> z mod nat v = b mod nat v\<close>
    from t2 pre1 have t31: "nat v\<ge>4 \<and> nat u\<ge>1" by auto
    from t31 have t3: "nat v*nat u\<ge>4" using mult_le_mono by fastforce
    define w::nat where "w=z+ nat u*nat v"
    from w_def t3 have t4: "w\<ge>4" by (simp add: mult.commute)
    have t51: "(nat u*nat v) mod nat u = 0 \<and> (nat u*nat v) mod nat v = 0" using algebra by simp
    from t51 w_def have t5: "w mod nat u = z mod nat u" by presburger
    from t51 w_def have t6: "w mod nat v = z mod nat v" by presburger
    from t5 t6 zdef have t7: "w mod nat u = 2 mod nat u \<and> w mod nat v = b mod nat v"  by simp
    from t7 t31 have t8: "int w mod u = 2 mod u \<and> int w mod v = int b mod v" 
      using nat_int1 nat_int2 by force
    from t4 t8 show ?thesis by force
  qed
  obtain w::nat where "int w mod u = 2 mod u \<and> int w mod v = int b mod v \<and> w>2" using wdef by force
  note wd = \<open>int w mod u = 2 mod u \<and> int w mod v = int b mod v \<and> w>2\<close>
  define x where "x = \<alpha> w c"
  define y where "y = \<alpha> w (c+1)"
  from alpha_det1 wd x_def y_def have 350: "x^2-int w*x*y+y^2 =1" by (metis add_gr_0 alpha_det2 diff_add_inverse2 less_one mult.assoc)
  from x_def wd congruence have 353: "a mod v = x mod v"
    by (smt "374" assms int_nat_eq nat_int nat_mod_distrib)
  from congruence2 wd x_def have 379: "x mod int (w-2) = int c mod (int w-2)"
    using int_ops(6) zmod_int by auto
  from wd have wc: "u dvd (int w-2)" using mod_diff_cong mod_eq_0_iff_dvd by fastforce
  from wc have wb: "\<exists>k1. u*k1=int w-2" by (metis dvd_def)
  obtain k1 where "u*k1=int w-2" using wb by force
  note k1def = \<open>u*k1=int w-2\<close>
  define r1 where "r1=int c mod (int w-2)"
  from r1_def 379 have wa: "r1 = x mod (int w-2)"
    using int_ops(6) wd by auto
  obtain k2 where "int c = (int w-2)*k2+r1" by (metis mult_div_mod_eq r1_def)
  note k2def = \<open>int c = (int w-2)*k2+r1\<close>
  from k2def k1def have a355: "int c = u*k1*k2+r1" by simp
  from udef k1def k2def have bh: "u*k1*k2 mod u = 0" by (metis mod_mod_trivial mod_mult_left_eq mod_mult_self1_is_0 mult_eq_0_iff)
  from a355 bh have b355: "(u*k1*k2+r1) mod u = r1 mod u" by (simp add: mod_eq_dvd_iff)
  from a355 b355 have c355: "int c mod u = r1 mod u" by simp
  from wa have waa: "\<exists>k3. x = k3*(int w-2)+r1" by (metis div_mult_mod_eq)
  obtain k3 where "x=k3*(int w-2)+r1" using waa by force
  from k1def \<open>x = k3*(int w-2)+r1\<close> have d355: "x=u*k1*k3+r1" by simp
  from udef k1def have ch: "u*k1*k3 mod u = 0" by (metis mod_mod_trivial mod_mult_left_eq mod_mult_self1_is_0 mult_eq_0_iff)
  from d355 ch have e355: "(u*k1*k3+r1) mod u = r1 mod u" by (simp add: mod_eq_dvd_iff)
  from d355 e355 have f355: "x mod u = r1 mod u" by simp
  from c355 f355 have 355: "int c mod u = x mod u" by simp
  from assms s1 wdef udef 343 344 345 v_def wd 350 376 353 354 355 have prefinal: "u^2-b*u*t+t^2=1 \<and> s^2-b*s*r+r^2=1 \<and> r<s
         \<and> u^2 dvd s \<and> b*s=v+2*r \<and> w mod v = b mod v \<and> w mod u = 2 mod u \<and> w>2 \<and> x^2-w*x*y+y^2=1 \<and>
         2*a<u \<and> 2*a<v \<and> a mod v = x mod v \<and> 2*c<u \<and> c mod u = x mod u" by fastforce
  from alpha_strictly_increasing have s_pos: "s\<ge>0" using asd s_def by linarith
  define S where "S=nat s"
  from alpha_strictly_increasing have r_pos: "r\<ge>0" using asd r_def by (smt One_nat_def Suc_1 alpha_superlinear assms(1) lessI less_trans numeral_3_eq_3 of_nat_0_le_iff)
  define R where "R=nat r"
  from udef alpha_strictly_increasing have ut_pos:"u\<ge>0 \<and> t\<ge>0" using pre1 by linarith
  from assms have a_pos: "a\<ge>0" using a354 by linarith
  from a_pos have v_pos: "v\<ge>0" using "376" by linarith
  from x_def y_def have xy_pos: "x\<ge>0 \<and> y\<ge>0" by (smt alpha_superlinear of_nat_0_le_iff wd)
  define U where "U=nat u"
  define T where "T=nat t"
  define V where "V=nat v"
  define X where "X=nat x"
  define Y where "Y=nat y"
  from lem U_def T_def S_def R_def X_def Y_def prefinal have lem1: "U^2+T^2=1+b*U*T \<and> S^2+R^2=1+b*S*R \<and> X^2+Y^2=1+w*X*Y" using s_pos ut_pos r_pos xy_pos by blast
  from R_def S_def have lem2: "R<S" using r_def s_def r_pos s_pos using s212 by linarith
  from U_def S_def have lem3: "U^2 dvd S" using 345 ut_pos s_pos
    by (metis int_dvd_int_iff int_nat_eq of_nat_power)
  have aq: "int b*s\<ge>2*r" using v_def v_pos by simp
  from aq have aq1: "nat (int b*s) \<ge> nat (2*r)" by simp
  from s_pos r_pos assms have aq2: "nat (int b*s) = b*(nat s) \<and> nat (2*r) = 2*(nat r)" by (simp add: nat_mult_distrib)
  from aq1 aq2 have aq3: "b*S\<ge>2*R" using S_def R_def by simp
  from aq3 have aq4: "int (b*S-2*R) = int (b*S)-int (2*R)" using of_nat_diff by blast
  have aq5: "int (b*S) = int b*int S \<and> int (2*R) = 2*int R" by simp
  from aq4 aq5 have aq6: "int (b*S-2*R) = int b*s-2*r" using R_def S_def r_pos s_pos by simp
  from aq6 v_def v_pos V_def have lem4: "b*S-2*R = V" by simp
  from prefinal v_pos V_def ut_pos U_def xy_pos X_def a_pos have lem5: "w mod V = b mod V \<and> w mod U = 2 mod U \<and> a mod V=X mod V \<and> c mod U = X mod U"
    by (metis int_nat_eq nat_int of_nat_numeral zmod_int)
  from a_pos ut_pos v_pos U_def V_def prefinal have lem6: "2*nat a<U \<and> 2*nat a<V \<and> 2*c<U" by auto
  from prefinal have lem7: "w>2" by simp
  have third_last: "\<forall>b s v r::nat. b * s = v + 2 * r \<longleftrightarrow> int (b * s) = int (v + 2 * r)" using of_nat_eq_iff by blast
  have onemore: "\<forall>u t b. u ^ 2 + t ^ 2 = 1 + b * u * t \<longleftrightarrow> int u ^ 2 + int t ^ 2 = 1 + int b * int u * int t"
    by (metis (no_types) nat_int of_nat_1 of_nat_add of_nat_mult of_nat_power)
  from lem1 lem2 lem3 lem4 lem5 lem6 lem7 third_last onemore show ?thesis
    unfolding Exp_Matrices.alpha_equations_def[of a b c] apply auto
    using assms apply blast
    apply (rule exI[of _ R], rule exI[of _ S], rule exI[of _ T], rule exI[of _ U], simp)
    apply (rule exI[of _ V], simp)
    apply (rule exI[of _ w], simp)
    apply (rule exI[of _ X], simp)
    using aq4 aq5 lem5 by auto
qed

subsubsection \<open>Exponentiation is Diophantine\<close>

text \<open>Equations 3.80-3.83\<close>

lemma 86:
  fixes b r and q::int
  defines "m \<equiv> b * q - q * q - 1"
  shows "(q * \<alpha> b (r + 1) - \<alpha> b r) mod m = (q ^ (r + 1)) mod m"
proof(induction r)
  case 0
  show ?case by simp
next
  case (Suc n)
  from m_def have a0: "(q * q - b * q + 1) mod m =  ((-(q * q - b * q + 1)) mod m + (q * q - b * q + 1) mod m) mod m" by simp
  have a1: "\<dots> = 0" by (simp add:mod_add_eq)
  from a0 a1 have a2: "(q * q - b * q + 1) mod m = 0" by simp

  from a2 have b0: "(b * q - 1) mod m = ((q * q - b * q + 1) mod m + (b * q - 1) mod m) mod m" by simp
  have b1: "\<dots> = (q * q) mod m" by (simp add: mod_add_eq)
  from b0 b1 have b2: "(b * q - 1) mod m =  (q * q) mod m" by simp

  have "(q * (\<alpha> b (Suc n + 1)) -\<alpha> b (Suc n)) mod m = (q * (int b *\<alpha> b (Suc n) -\<alpha> b n) -\<alpha> b (Suc n)) mod m" by simp
  also have "\<dots> = ((b * q - 1) *\<alpha> b (Suc n) - q *\<alpha> b n) mod m" by algebra
  also have "\<dots> = (((b * q - 1) *\<alpha> b (Suc n)) mod m - (q *\<alpha> b n) mod m) mod m" by (simp add: mod_diff_eq)
  also have "\<dots> = ((((b * q - 1) mod m) * ((\<alpha> b (Suc n)) mod m)) mod m - (q *\<alpha> b n) mod m) mod m" by (simp add: mod_mult_eq)
  also have "\<dots> = ((((q * q) mod m) * ((\<alpha> b (Suc n)) mod m)) mod m - (q *\<alpha> b n) mod m) mod m" by (simp add: b2)
  also have "\<dots> = (((q * q) * (\<alpha> b (Suc n))) mod m - (q *\<alpha> b n) mod m) mod m" by (simp add: mod_mult_eq)
  also have "\<dots> = ((q * q) * (\<alpha> b (Suc n)) - q *\<alpha> b n) mod m" by (simp add: mod_diff_eq)
  also have "\<dots> = (q * (q * (\<alpha> b (Suc n)) -\<alpha> b n)) mod m" by algebra
  also have "\<dots> = ((q mod m) * ((q * (\<alpha> b (Suc n)) -\<alpha> b n) mod m)) mod m" by (simp add: mod_mult_eq)
  finally have c0: "(q * (\<alpha> b (Suc n + 1)) -\<alpha> b (Suc n)) mod m = ((q mod m) * ((q * (\<alpha> b (Suc n)) -\<alpha> b n) mod m)) mod m" by simp
  from Suc.IH have c1: "\<dots> = ((q ^ (n + 2))) mod m" by (simp add: mod_mult_eq)

  from c0 c1 show ?case by simp
qed

text \<open>This is a more convenient version of (86)\<close>

lemma 860:
  fixes b r and q::int
  defines "m \<equiv> b * q - q * q - 1"
  shows "(q * \<alpha> b r - (int b * \<alpha> b r -  \<alpha> b (Suc r))) mod m = (q ^ r) mod m"
proof(cases "r=0")
  case True
  then show ?thesis by simp
next
  case False
  thus ?thesis using alpha_n[of b "r-1"] 86[of q b "r-1"] m_def by auto 
qed

text \<open>We modify the equivalence (88) in a similar manner\<close>

lemma 88:
  fixes b r p q:: nat
  defines "m \<equiv> int b * int q - int q * int q - 1"
  assumes "int q ^ r < m" and "q > 0"
  shows "int p = int q ^ r \<longleftrightarrow> int p < m  \<and>  (q * \<alpha> b r - (int b * \<alpha> b r -  \<alpha> b (Suc r))) mod m = int p mod m"
  using "Exp_Matrices.860" assms(2) m_def by auto

lemma 89:
  fixes r p q :: nat
  assumes "q > 0"
  defines "b \<equiv> nat (\<alpha> (q + 4) (r + 1)) + q * q + 2"
  defines "m \<equiv> int b * int q - int q * int q - 1"
  shows "int q ^ r < m"
proof -
  have a0: "int q * int q - 2 * int q + 1 = (int q - 1) * (int q - 1)" by algebra
  from assms have a1: "int q * int q * int q \<ge> int q * int q" by simp
  from assms a0 a1 have a2: "\<dots> > (int q - 1) * (int q - 1)" by linarith

  from alpha_strictly_increasing have c0: " \<alpha> (q + 4) (r + 1) > 0" by simp
  from c0 have c1: " \<alpha> (q + 4) (r + 1) = int (nat (\<alpha> (q + 4) (r + 1)))" by simp

  then have b1: "(q+3) ^ r \<le>  \<alpha> (q + 4) (r + 1)" using alpha_exponential_1[of "q+3"]
    by(auto simp add: add.commute)
  have b3: "int q ^ r \<le> (q + 3) ^ r" by (simp add: power_mono)
  also have b4: "... \<le> (q + 3) ^ r * int q" using assms by simp
  also from assms b1 have b5: "\<dots> \<le>  \<alpha> (q + 4) (r + 1) * int q" by simp
  also from a2 have b6: "\<dots> <  \<alpha> (q + 4) (r + 1) * int q + int q * int q * int q - (int q - 1) * (int q - 1)" by simp
  also have b7: "\<dots> = ( \<alpha> (q + 4) (r + 1) + int q * int q + 2) * q - int q * int q - 1" by algebra
  also from assms m_def have b8: "\<dots> = m"  using c1 by auto
  finally show ?thesis by linarith
qed
end

text \<open>The final equivalence\<close>
theorem exp_alpha:
  fixes p q r :: nat
  shows "p = q ^ r \<longleftrightarrow> ((q = 0 \<and> r = 0 \<and> p = 1) \<or> 
                          (q = 0 \<and> 0 < r \<and> p = 0) \<or> 
                          (q > 0 \<and> (\<exists>b m.
                            b =  Exp_Matrices.\<alpha> (q + 4) (r + 1) + q * q + 2 \<and> 
                            m = b * q - q * q - 1 \<and> 
                            p < m \<and> 
                            p mod m = ((q * Exp_Matrices.\<alpha> b r) - (int b * Exp_Matrices.\<alpha> b r  - Exp_Matrices.\<alpha> b (r + 1))) mod m)))"
proof(cases "q>0")
  case True
  show ?thesis (is "?P = ?Q")
  proof (rule)
    assume ?P
    define b where "b = nat (Exp_Matrices.\<alpha> (q + 4) (r + 1)) + q * q + 2"
    define m where "m = int b * int q - int q * int q - 1"
    have sg1: "int b = Exp_Matrices.\<alpha> (q + 4) (Suc r) + int q * int q + 2" using b_def 
    proof-
      have "0 \<le> (Exp_Matrices.\<alpha> (q + 4) (r + 1))" using Exp_Matrices.alpha_exponential_1[of "q+3" r] 
         apply (simp add: add.commute) using zero_le_power[of "int q+3" r] by linarith
      then show ?thesis using b_def int_nat_eq[of "(Exp_Matrices.\<alpha> (q + 4) (r + 1))"] by simp
    qed
    have sg2: "q ^ r < b * q - Suc (q * q)" using True "Exp_Matrices.89"[of q r] 
        of_nat_less_of_nat_power_cancel_iff[of q r " b * q - Suc (q * q)"] 
        b_def int_ops(6)[of "b * q" "Suc (q * q)"] of_nat_1 of_nat_add of_nat_mult plus_1_eq_Suc by smt
    have sg3: "int (q ^ r mod (b * q - Suc (q * q)))
               = (int q * Exp_Matrices.\<alpha> b r - (int b * Exp_Matrices.\<alpha> b r - Exp_Matrices.\<alpha> b (Suc r)))
                                                mod int (b * q - Suc (q * q))"
    proof-
      have "int b * int q - int q * int q - 1 = b * q - Suc (q * q)"
        using \<open>q ^ r < b * q - Suc (q * q)\<close> int_ops(6) by auto
      then show ?thesis using "Exp_Matrices.860"[of q b r] by (simp add: zmod_int)
    qed
    from sg1 sg2 sg3 True show ?Q
      by (smt (verit) Suc_eq_plus1_left \<open>p = q ^ r\<close> add.commute diff_diff_eq of_nat_mult)
  next
    assume Q: ?Q (is "?A \<or> ?B \<or> ?C")
    thus ?P
      proof (elim disjE)
      show "?A \<Longrightarrow> ?P" by auto
      show "?B \<Longrightarrow> ?P" by auto
      show "?C \<Longrightarrow> ?P"
      proof-
        obtain b where b_def: "int b = Exp_Matrices.\<alpha> (q + 4) (Suc r) + int q * int q + 2" using Q True by auto
        have prems3: "p < b * q - Suc (q * q)" using Q True b_def apply (simp add: add.commute) by (metis of_nat_eq_iff)
        have prems4: " int p = (int q * Exp_Matrices.\<alpha> b r - ((Exp_Matrices.\<alpha> (q + 4) (Suc r) + 
          int q * int q + 2) * Exp_Matrices.\<alpha> b r - Exp_Matrices.\<alpha> b (Suc r))) mod int (b * q - Suc (q * q))"
          using  Q True b_def apply (simp add: add.commute) by (metis mod_less of_nat_eq_iff) 
        define m where "m = int b * int q - int q * int q - 1"
        have "int q ^ r < int b * int q - int q * int q - 1" using "Exp_Matrices.89"[of q r] b_def True 
          by (smt Exp_Matrices.alpha_strictly_increasing One_nat_def Suc_eq_plus1 int_nat_eq nat_2 
              numeral_Bit0 of_nat_0_less_iff of_nat_add of_nat_mult one_add_one)
        moreover have "int p < m" by (smt gr_implies_not0 int_ops(6) int_ops(7) less_imp_of_nat_less 
               m_def of_nat_Suc of_nat_eq_0_iff prems3)
        moreover have "(int q * Exp_Matrices.\<alpha> b r - (int b * Exp_Matrices.\<alpha> b r - Exp_Matrices.\<alpha> b (Suc r))) mod m = int p mod m" 
          using prems4 by (smt calculation(2) int_ops(6) m_def mod_pos_pos_trivial of_nat_0_le_iff 
              of_nat_1 of_nat_add of_nat_mult plus_1_eq_Suc b_def)
        ultimately show ?thesis using True "Exp_Matrices.88"[of q "r" b p] m_def  by simp
      qed
    qed
  qed
next
  case False
  then show ?thesis by auto
qed

lemma alpha_equivalence:
  fixes a b c
  shows "3 < b \<and> int a = Exp_Matrices.\<alpha> b c \<longleftrightarrow> (\<exists>r s t u v w x y. Exp_Matrices.alpha_equations a b c r s t u v w x y)"
  using Exp_Matrices.alpha_equiv_suff Exp_Matrices.alpha_equiv_nec
  by meson+

end