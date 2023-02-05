theory Digits_int
  imports 
    Complex_Main
begin
section \<open>Representation of Integers in Different Number Systems\<close>
text \<open>This file is an adaption of \<open>Van_der_Waerden/Digits.thy\<close> for representation of the
 Integers (instead of the natural numbers) in different number systems.
The main difference is the integer input in the function \<open>digit\<close>.\<close>
text \<open>First, we look at some useful lemmas for splitting sums. \<close>
lemma split_sum_first_elt_less: assumes "n<m" 
  shows "(\<Sum>i\<in>{n..<m}. f i) = f n + (\<Sum>i\<in>{Suc n ..<m}. f i)"
  using sum.atLeast_Suc_lessThan assms by blast

lemma split_sum_mid_less: assumes "i<(n::nat)"
  shows "(\<Sum>j<n. f j) = (\<Sum>j<i. f j) + (\<Sum>j=i..<n. f j)"
proof -
  have "(\<Sum>j<n. f j) = (\<Sum>j\<in>{..<i} \<union> {i..<n}. f j)"
    using \<open>i < n\<close> by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>j<i. f j) + (\<Sum>j=i..<n. f j)"
    by (subst sum.union_disjoint) auto
  finally show "(\<Sum>j<n. f j) = (\<Sum>j<i. f j) + (\<Sum>j=i..<n. f j)" .
qed

text \<open>In order to use representation of numbers in a basis \<open>base\<close> and to calculate the conversion 
to and from integers, we introduce the following locale.\<close>
locale digits =
  fixes base :: int
  assumes base_pos: "base > 0"
begin

text \<open>Conversion from basis base to integers: \<open>from_digits n d\<close>

\begin{tabular}{lcp{8cm}}
  n:& \<open>nat\<close>& length of representation in basis base\\
  d:& \<open>nat \<Rightarrow> nat\<close>& function of digits in basis base where \<open>d i\<close> is the $i$-th digit in basis base\\
  output:& \<open>nat\<close>& natural number corresponding to $d(n-1) \dots d(0)$ as integer\\
\end{tabular}
\<close>
fun from_digits :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "from_digits 0 d = 0"
| "from_digits (Suc n) d = d 0 + nat base * from_digits n (d \<circ> Suc)"

text \<open>Alternative definition using sum:\<close>
lemma from_digits_altdef: "from_digits n d = (\<Sum>i<n. d i * nat base ^ i)"
  by (induction n d rule: from_digits.induct)
     (auto simp add: sum.lessThan_Suc_shift o_def sum_distrib_left 
       sum_distrib_right mult_ac simp del: sum.lessThan_Suc)

lemma int_from_digits:
  "int (from_digits n d) = (\<Sum>i<n. int (d i) * base ^ i)"
unfolding from_digits_altdef using base_pos by auto

text \<open>Digit in basis base of some integer number: \<open>digit x i\<close>

\begin{tabular}{lcp{8cm}}
  x:& \<open>int\<close>& integer\\
  i:& \<open>nat\<close>& index\\
  output:& \<open>int\<close>& $i$-th digit of representation in basis base of $x$\\
\end{tabular}
\<close>
fun digit :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "digit x 0 = \<bar>x\<bar> mod base"
| "digit x (Suc i) = digit (\<bar>x\<bar> div base) i"

text \<open>Alternative definition using divisor and modulo:\<close>
lemma digit_altdef: "digit x i = ( \<bar>x\<bar> div (base ^ i)) mod base"
proof (induction x i rule: digit.induct)
  case (2 x i)
  show ?case by (subst digit.simps(2), subst 2) (smt (verit, ccfv_SIG) base_pos 
        pos_imp_zdiv_neg_iff power.simps(2) zdiv_zmult2_eq zero_less_power)
qed simp

text \<open>Every digit must be smaller that the base.\<close>
lemma digit_less_base: "digit x i < base"
  using base_pos by (auto simp: digit_altdef)

text \<open>A representation in basis \<open>base\<close> of length $n$ must be less than $\<open>base\<close> ^ n$.\<close>
lemma from_digits_less: 
  assumes "\<forall>i<n. d i < base" 
  shows "from_digits n d < base ^ n"
using assms proof (induct n d rule: from_digits.induct)
  case (2 n d)
  have "from_digits n (d \<circ> Suc) \<le> base ^ n -1" using 2 
    by (simp add: "2.hyps")
  moreover have "d 0 \<le> base -1" using 2 by simp
  ultimately have "d 0 + base * from_digits n (d \<circ> Suc) \<le> 
      base - 1 + base * (base^(n) - 1)" 
    by (smt (verit, ccfv_SIG) base_pos mult_less_cancel_left_pos)
  then show "from_digits (Suc n) d < base ^ Suc n" 
    using base_pos by (simp add: right_diff_distrib)
qed auto


text \<open>Lemmas for \<open>mod\<close> and \<open>div\<close> in number systems of basis \<open>base\<close>:\<close>
lemma mod_base:  assumes "\<And>i. i<n \<Longrightarrow> d i < base" "n>0"
  shows "from_digits n d mod base = d 0 "
proof -
  have "(\<Sum>i<n. d i * base ^ i) mod base = 
          (\<Sum>i<n. d i * base ^ i mod base) mod base"  
  by (subst mod_sum_eq[symmetric]) simp
  then show ?thesis using assms 
    sum.lessThan_Suc_shift[of "(\<lambda>i. d i * base ^ i mod base)" "n-1"]
    int_from_digits by simp
qed

lemma mod_base_i:  
  assumes "\<And>i. i<n \<Longrightarrow> (d i ::nat) < base" "n>0" "i<n"
  shows "(\<Sum>j=i..<n. d j * base ^ (j-i)) mod base = d i "
proof -
  have eq: "(\<Sum>j=i..<n. d j * base ^ (j-i)) mod base = 
        (\<Sum>j=i..<n. d j * base ^ (j-i) mod base) mod base"  
    by (subst mod_sum_eq[symmetric]) simp
  then show ?thesis  using assms 
    split_sum_first_elt_less[where  f = "(\<lambda>j. d j * base ^ (j-i) mod base)"]
    int_from_digits by auto
qed


lemma div_base_i: 
  assumes "\<And>i. i<n \<Longrightarrow> (d i::nat) < base" "n>0" "i<n"
  shows "from_digits n d div (base ^i) = (\<Sum>j=i..<n. d j * base ^ (j-i))"
  unfolding int_from_digits proof -
  have base_exp: "base^(j) =  base^(j-i) * base^i" 
    if "j\<in>{i..<n}" for j 
    by (metis Nat.add_diff_assoc2 add_diff_cancel_right' atLeastLessThan_iff 
        power_add that)
  have first:"(\<Sum>j<i. d j * base ^ j)< base ^ i" 
    using assms from_digits_less[where n="i"] 
    unfolding int_from_digits by auto
  have ge_0: "0 \<le> (\<Sum>j<i. int (d j) * base ^ j)" using base_pos
  by (metis int_from_digits of_nat_0_le_iff)
  have eq: "(\<Sum>j<n. d j * base ^ j) = 
          (\<Sum>j<i. d j * base ^ j) + (\<Sum>j=i..<n. d j * base ^ j)" 
    using assms split_sum_mid_less[where f="(\<lambda>j. d j * base^j)"] by auto
  have split_sum: "(\<Sum>j<n. d j * base ^ j) = 
      (\<Sum>j<i. d j * base ^ j) + base^i * (\<Sum>j=i..<n. d j * base ^ (j-i))"
    unfolding eq using base_exp mult.assoc sum_distrib_right
    by (smt (z3) mult.commute sum.cong)
  show "(\<Sum>i<n. d i * base ^ i) div base ^ i = 
             (\<Sum>j = i..<n. d j * base ^ (j - i))" 
    unfolding split_sum using base_pos first div_pos_pos_trivial[OF ge_0 first]
    by (subst div_mult_self2, auto)
qed



text \<open>Conversions are inverse to each other.\<close>
lemma digit_from_digits:
  assumes "\<And>j. j<n \<Longrightarrow> d j < base" "n>0" "i<n"
  shows   "digit (from_digits n d) i = d i"
  using assms proof (cases "i=0")
  case True
  then show ?thesis
  using assms(1) assms(3) mod_base by force
next
  case False
  have "from_digits n d div base^i mod base = d i" 
    using assms by (auto simp add: div_base_i mod_base_i) 
  then show "digit (from_digits n d) i = d i" 
    unfolding digit_altdef by auto
qed

lemma div_distrib: assumes "i<n" 
  shows "(a*base^n + b) div base^i mod base = b div base^i mod base"
proof -
  have "base^i dvd (a*base^n)" using assms 
    by (simp add: le_imp_power_dvd)
  moreover have "a*base^n div base^i mod base = 0" 
    by (metis Suc_leI assms dvd_imp_mod_0 dvd_mult 
        dvd_mult_imp_div le_imp_power_dvd power_Suc)
  ultimately show ?thesis
    by (metis add.right_neutral div_mult_mod_eq 
        div_plus_div_distrib_dvd_left mod_mult_self3)
qed


lemma(in digits) digits_eq_0:
  assumes "x = 0"
  shows "digit x i = 0"
by (simp add: assms digit_altdef)
end


lemma split_digits_eq_zero:
  assumes "a + base * b = 0" "\<bar>a\<bar><base" "(base::int)>2"
  shows "a = 0 \<and> b=0"
using assms proof (cases "b = 0")
  case True
  then show "a=0 \<and> b=0" using assms by auto
next
  case False
  then have "\<bar>b\<bar> \<ge> 1" by auto
  then have "\<bar>a\<bar> < \<bar>base * b\<bar>" using assms(2) assms(3)
    by (subst abs_mult) (smt (verit) mult_le_cancel_left1)
  moreover have "\<bar>a\<bar> = \<bar>base * b\<bar>" using assms(1) by auto
  ultimately have False by auto
  then show ?thesis by auto
qed


lemma respresentation_in_basis_eq_zero:
  assumes "(\<Sum>i<n. c i * base^i) = 0" "(base::int) > 2" "\<And>i. i<n \<Longrightarrow> \<bar>c i\<bar> < base" "i<n"
  shows "c i = 0"
using assms proof (induction n arbitrary: i c)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have eq_0: "c 0 + base * (\<Sum>i<n. c (i+1) * base ^ i) = 0" 
    using Suc(2) unfolding sum.lessThan_Suc_shift power_Suc sum.cong[of "{..<n}" "{..<n}" 
      "(\<lambda>i. c (Suc i) * (base * base ^ i))" "(\<lambda>i. base * (c (n + 1) * base ^ n))"]
    by (subst sum_distrib_left)(metis (no_types, lifting) Suc_eq_plus1 mult.left_commute 
      mult_cancel_left1 power_0 sum.cong)
  have "c 0 = 0 " and right: "(\<Sum>i<n. c (i+1) * base ^ i) = 0" 
    using split_digits_eq_zero[OF eq_0 Suc(4)[of 0] Suc(3)] by auto
  have lt_n: "c (i + 1) = 0" if "i<n" for i using Suc(4)
    by (subst Suc(1)[OF right \<open>2<base\<close> _ \<open>i<n\<close>], auto) 
  then show ?case
  proof (cases "i=0")
    case False
    then show ?thesis using Suc(5) lt_n less_Suc_eq_0_disj by auto
  qed (use \<open>c 0 = 0\<close> in \<open>auto\<close>)
qed

end