theory Lucas_Diophantine
  imports Lucas_Sequences
begin

subsection \<open>Lucas Sequences and Exponentiation\<close>

text \<open>Direct implication of lemma 3.12\<close>

lemma lucas_diophantine_dir:
  fixes A::int and B::nat
  shows "(3 * 2^B * \<psi> A B) mod (2*A-5) = (2 * (2^(2*B) - 1)) mod (2*A - 5)"
proof (induction B rule: \<psi>_induct)
  case 0
  then show ?case by auto
next
  case 1
  then show ?case by auto
next
  case (sucsuc B)
  note t = this
  have "12*2^B * (A*(\<psi> A (B+1)) - (\<psi> A B)) = 12*(2^B)*A*(\<psi> A (B+1)) - 12*(2^B)*(\<psi> A B)"
    by (simp add: right_diff_distrib)
  then have "12*2^B * (A*(\<psi> A (B+1)) - (\<psi> A B)) = 6*A*(2^(B+1))*(\<psi> A (B+1)) - 12*(2^B)*(\<psi> A B)"
    by simp
  then have e1:  "3 * (2^(B+2)) * (\<psi> A (B+2)) = 6*A*(2^(B+1))*(\<psi> A (B+1)) - 12*(2^B)*(\<psi> A B)"
    by auto

  have e2: " 2 * A * (3 * 2 ^ (B + 1) * \<psi> A (B + 1)) mod (2 * A - 5)
      = 2 * A * (2 * (2 ^ (2 * (B+1)) - 1)) mod (2 * A - 5)"
    using t mod_mult_cong[of "2*A" "2*A-5" "2*A" "3*(2^(B+1))*(\<psi> A (B+1))" "2*(2^(2*(B+1))-1)"]
    by auto
  have "6*A*(2^(B+1)) = 2 * A * (3 * 2 ^ (B + 1))"
    by auto
  then have e3: "6*A*(2^(B+1))*(\<psi> A (B+1)) =  2 * A * (3 * 2 ^ (B + 1) * \<psi> A (B + 1))"
    by auto
  have "4*A*(2^(2*(B+1))-1) =  2 * A * (2 * (2 ^ (2 * (B+1)) - 1))"
    by simp
  then have e4: "6*A*(2^(B+1))*(\<psi> A (B+1)) mod (2*A-5) = 4*A*(2^(2*(B+1))-1) mod (2*A-5)"
    using e2 e3 by metis

  have "3 * 2^B * (\<psi> A B) mod (2*A-5) = 2*(2^(2*B)-1) mod (2*A-5)"
    using t by auto
  have "12*(2^B)*(\<psi> A B) = 4* (3 * 2^B * (\<psi> A B))"
    by auto
  have "8*(2^(2*B)-1) = (4::int) * ( 2*(2^(2*B)-1))"
    by auto
  then  have e5: "12*(2^B)*(\<psi> A B) mod (2*A-5) = 8*(2^(2*B)-1) mod (2*A-5)"
    using t
    by (metis (no_types) \<open>12 * 2 ^ B * \<psi> A B = 4 * (3 * 2 ^ B * \<psi> A B)\<close> mod_mult_right_eq)
 
  then have "(6*A*(2^(B+1))*(\<psi> A (B+1)) - 12*(2^B)*(\<psi> A B)) mod (2*A-5)
      = (4*A*(2^(2*(B+1))-1) - 8*(2^(2*B)-1)) mod (2*A-5)"
    using e4 mod_diff_cong by blast
  then have e6: "3 * (2^(B+2)) * (\<psi> A (B+2)) mod (2*A-5)
      = (4*A*(2^(2*(B+1))-1) - 8*(2^(2*B)-1)) mod (2*A-5)"
    using e1 by auto

  have "\<And>k. 4*A*k = (4*A-10)*k + 10*k"
    by (metis diff_add_cancel mult.commute ring_class.ring_distribs(1))
  then have "4*A*(2^(2*(B+1))-1) = (4*A-10)*(2^(2*(B+1))-1) + 10 *(2^(2*(B+1))-1)"
    by auto
  then have "4*A*(2^(2*(B+1))-1) - 8*(2^(2*B)-1)
      = (4*A-10)*(2^(2*(B+1))-1) + 10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1)"
    by auto
  then have e7: "3 * (2^(B+2)) * (\<psi> A (B+2)) mod (2*A-5)
      = ((4*A-10)*(2^(2*(B+1))-1) + 10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1)) mod (2*A-5)"
    using e6 by presburger

  have "(4*A-10) mod (2*A-5) = 0"
    by (smt (z3) minus_mod_self2 mod_self)
  then have "(4*A-10)*(2^(2*(B+1))-1) mod (2*A-5) = 0"
    using mod_mult_cong by auto
  then have e8: "\<And>k. ((4*A-10)*(2^(2*(B+1))-1) +k) mod (2*A-5) = k mod (2*A-5)"
    by force
  have "((4*A-10)*(2^(2*(B+1))-1) + 10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1)) mod (2*A-5)
      = (10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1)) mod (2*A-5)"
    using e8[of "(10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1))"] by (smt (z3))
  then have e9: "3 * (2^(B+2)) * (\<psi> A (B+2)) mod (2*A-5)
      = (10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1)) mod (2*A-5)"
    using e7 by auto

  have e10: "10 *(2^(2*(B+1))-1) -8*(2^(2*B)-1) = 2*(2^(2*(B+2)) - (1::int))"
    by auto

  then show ?case using e9 e10 by auto
qed

text \<open>A few lemmas helping variable changes in sums\<close>

lemma translation_var_0_to_1:
  fixes f::"nat \<Rightarrow> int" and n::nat
  shows "(\<Sum>i=0..n. f (i+1)) = (\<Sum>i=1..n+1. (f i))"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by auto
qed

lemma chang_var2:
  fixes f::"nat \<Rightarrow> nat \<Rightarrow> int" and n::nat
  shows "(\<Sum>i=0..n. f (i+1) (n-i)) = (\<Sum>i=1..n+1. f i (n+1-i))"
proof -
  obtain g::"nat \<Rightarrow> int" where g_def: "\<And>i. i \<le> n+1 \<Longrightarrow> g i = f i (n+1-i)" by auto
  have "i \<le> n \<Longrightarrow> f (i+1) (n-i) = g (i+1)" for i
    by (auto simp add: g_def)
  then have "(\<Sum>i=0..n. f (i+1) (n-i)) = (\<Sum>i=0..n. g (i+1))"
    by auto
  also have "... = (\<Sum>i=1..n+1. g i)"
    using translation_var_0_to_1 by auto
  also have "... = (\<Sum>i=1..n+1. f i (n+1-i))"
    using g_def by auto
  finally show ?thesis.
qed

lemma chang_var3:
  fixes f::"nat \<Rightarrow> nat \<Rightarrow> int" and n::nat
  assumes "n\<ge>1"
  shows "(\<Sum>i=0..n-1. f (i+1) (n-i)) = (\<Sum>i=1..n. f i (n+1-i))"
proof -
  obtain g::"nat \<Rightarrow> int" where g_def: "\<And>i. i \<le> n \<Longrightarrow> g i = f i (n+1-i)" by auto
have "i \<le> n-1 \<Longrightarrow> f (i+1) (n-i) = g (i+1)" for i
    using assms by (auto simp add: g_def)
  then have "(\<Sum>i=0..n-1. f (i+1) (n-i)) = (\<Sum>i=0..n-1. g (i+1))"
    by auto
  also have "... = (\<Sum>i=1..n. g i)"
    using translation_var_0_to_1[of g "n-1"] assms by auto
  also have "... = (\<Sum>i=1..n. f i (n+1-i))"
    using g_def by auto
  finally show ?thesis.
qed

text \<open>Lemma 3.11, requiring no other result, but necessary to the proof of the reciprocal implication\<close>

definition f_38:: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where "f_38 U V a b = U^(2*a)*V^(2*b)"

lemma lucas_exponential_diophantine:
  fixes A::int and B::nat and U::int and V::int
  assumes "B>0"
  shows "(U*V)^(B-1) * \<psi> A B mod (U^2 - A*U*V + V^2)
      = (\<Sum>r=0..(B-1). (U^(2*r))*(V^(2*(B-1-r)))) mod (U^2 - A*U*V + V^2)"
proof -
  have f0: "b=0 \<or> (U*V)^(b-1) * \<psi> A b mod (U^2 - A*U*V + V^2)
      = (\<Sum>r=0..(b-1). (U^(2*r))*(V^(2*(b-1-r)))) mod (U^2 - A*U*V + V^2)" for b
proof (induction b rule: \<psi>_induct_strict)
  case 0
  show ?case using assms by auto
  case 1
  then show ?case by auto
next
  case 2
  have "(U * V) ^ (2 - 1) * \<psi> A 2 mod (U\<^sup>2 - A * U * V + V\<^sup>2) = U*V*\<psi> A (1+1) mod (U^2 - A*U*V + V^2)"
    by (metis add_diff_cancel_left' one_add_one power_one_right)
  also have "... = U*V*A mod (U^2 - A*U*V + V^2)"
    by auto
  also have "... = (U^2+V^2 - (U^2 - A*U*V + V^2))  mod (U^2 - A*U*V + V^2)"
    by (simp add: algebra_simps)
  also have "... = (U^2+V^2) mod (U^2 - A*U*V + V^2)"
    using minus_mod_self2 by blast
  also have "... = (U^(2*0)*V^(2*(2-1-0)) + U^(2*1)*V^(2*(2-1-1))) mod (U^2-A*U*V+V^2)"
    by (simp add: algebra_simps power2_eq_square)
  also have "... = (\<Sum>r=0..(2-1). (U^(2*r))*(V^(2*(2-1-r)))) mod (U^2 - A*U*V + V^2)"
    by auto
  finally have "(U * V) ^ (2 - 1) * \<psi> A 2 mod (U\<^sup>2 - A * U * V + V\<^sup>2)
      = (\<Sum>r=0..(2-1). (U^(2*r))*(V^(2*(2-1-r)))) mod (U^2 - A*U*V + V^2)".
  then show ?case by auto
next
  case (sucsuc b)
  note t = this
  have "(U * V) ^ (b + 2 - 1) * \<psi> A (b + 2) mod (U\<^sup>2 - A * U * V + V\<^sup>2)
      = (U*V)^(b+1)*(A*\<psi> A (b+1) - \<psi> A b) mod (U^2 - A*U*V + V^2)"
    by auto
  also have "... = ((A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1) - (U*V)^2*(U*V)^(b-1)*\<psi> A b) mod (U^2 - A*U*V + V^2)"
    apply (simp add: algebra_simps)
    by (smt (verit, best) One_nat_def Suc_1 ab_semigroup_mult_class.mult_ac(1) mult.left_commute
        not_gr_zero numeral_1_eq_Suc_0 numeral_plus_numeral plus_1_eq_Suc power_Suc0_right
        power_add_numeral2 power_eq_if sucsuc.hyps)
  finally have e1: "(U * V) ^ (b + 2 - 1) * \<psi> A (b + 2) mod (U\<^sup>2 - A * U * V + V\<^sup>2)
      = ((A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1) - (U*V)^2*(U*V)^(b-1)*\<psi> A b) mod (U^2 - A*U*V + V^2)".

  have e21: "(A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1) mod (U^2 - A*U*V +V^2)
      = (A*U*V)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))) mod (U^2 - A*U*V + V^2)"
    using t mod_mult_cong[of "A*U*V" "U^2-A*U*V+V^2" "A*U*V" "(U*V)^(b+1-1)*\<psi> A (b+1)"
        "\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))"]
    by (auto simp add: algebra_simps)
  also have " A*U*V mod (U^2-A*U*V+V^2) = (U^2+V^2) mod (U^2-A*U*V+V^2)"
    by (smt (z3) minus_mod_self2)
  then have "((A*U*V)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r))))) mod (U^2 - A*U*V + V^2)
      = ((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r))))) mod (U^2 - A*U*V + V^2)"
    using mod_mult_cong[of "(A*U*V)" "(U^2 -A*U*V + V^2)" "(U^2 + V^2)"
        "(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r))))" "(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r))))"]
    by force
  then have e22: "(A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1) mod (U^2 - A*U*V +V^2)
      = ((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r))))) mod (U^2 - A*U*V + V^2)"
    using e21 by auto

  have "(U*V)^2*(U*V)^(b-1)*\<psi> A b mod (U^2-A*U*V+V^2)
      = (U*V)^2*(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-1-r))) mod (U^2-A*U*V+V^2)"
    using t mod_mult_cong[of "(U*V)^2" "(U^2-A*U*V+V^2)" "(U*V)^2"
        "(U*V)^(b-1)*\<psi> A b" "(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-1-r)))"]
    by (auto simp add: algebra_simps)

  then have e2: "((A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1) - ((U*V)^2*(U*V)^(b-1)*\<psi> A b)) mod (U^2 - A*U*V +V^2)
      = (((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))))
      - (U*V)^2*(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-1-r)))) mod (U^2 - A*U*V +V^2)"
    using mod_diff_cong[of "(A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1)" "(U^2 - A*U*V +V^2)"
        "((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))))" "((U*V)^2*(U*V)^(b-1)*\<psi> A b)"
        "(U*V)^2*(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-1-r)))"] e22 by auto

  have U_sq_f: "a^2*f_38 a b i j = f_38 a b (i+1) j" for a b i j
  proof -
    have "a^2*f_38 a b i j = a^2*a^(2*i)*b^(2*j)" using f_38_def by auto
    also have "... = a^(2*(i+1))*b^(2*j)"
      by (metis distrib_left_numeral mult.commute nat_mult_1_right power_add)
    also have "... = f_38 a b (i+1) j" using f_38_def by auto
    finally show ?thesis.
  qed
  have f_comm: "f_38 a b i j = f_38 b a j i" for a b i j
  proof -
    have "f_38 a b i j = a^(2*i)*b^(2*j)" using f_38_def by auto
    also have "... = f_38 b a j i" using f_38_def by auto
    finally show ?thesis.
  qed
  have V_sq_f: "b^2*f_38 a b i j = f_38 a b i (j+1)" for a b i j
  proof -
    have "b^2*f_38 a b i j = b^2*f_38 b a j i"
      using f_comm by auto
    also have "... = f_38 b a (j+1) i"
      using U_sq_f by auto
    also have "... = f_38 a b i (j+1)" using f_comm by auto
    finally show ?thesis.
  qed

  have e31: "((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))))
      = ((U^2+V^2)*(\<Sum>r=0..(b+1-1). f_38 U V r (b-r)))"
    using f_38_def by auto
  have e32: "... = (\<Sum>r=0..(b+1-1). ((U^2+V^2)*f_38 U V r (b-r)))"
    using  Groups_Big.semiring_0_class.sum_distrib_left by auto
  have e33: "... = (\<Sum>r=0..(b+1-1). (U^2*f_38 U V r (b-r) + V^2*f_38 U V r (b-r)))"
   by (auto simp add: algebra_simps)
  have e34: "... = (\<Sum>r=0..(b+1-1). U^2*f_38 U V r (b-r)) + (\<Sum>r=0..(b+1-1). V^2*f_38 U V r (b-r))"
    by (auto simp add: algebra_simps Groups_Big.comm_monoid_add_class.sum.distrib)
    have "r \<le> b \<Longrightarrow> Suc b - r = Suc (b-r)" for r
      by auto
    then have "(\<Sum>r = 0..b. f_38 U V r (Suc (b - r))) = (\<Sum>r = 0..b. f_38 U V r (Suc b - r))"
      by auto
    then have e35: "(\<Sum>r=0..(b+1-1). U^2*f_38 U V r (b-r)) + (\<Sum>r=0..(b+1-1). V^2*f_38 U V r (b-r))
         = (\<Sum>r=0..(b+1-1). f_38 U V (r+1) (b-r)) + (\<Sum>r=0..(b+1-1). f_38 U V r (b+1-r))"
      by (auto simp add: U_sq_f V_sq_f)
    have e36: "... = (\<Sum>r=1..b+1. f_38 U V r (b+1-r)) + (\<Sum>r=0..b. f_38 U V r (b+1-r))"
      using chang_var2 by auto
    have e37: "... = (\<Sum>r=1..b+1. f_38 U V r (b+1-r)) + (\<Sum>r=0..b+1. f_38 U V r (b+1-r))
        - f_38 U V (b+1) 0"
      by auto
    have e310: "... = (\<Sum>r=1..b. f_38 U V r (b+1-r)) + (\<Sum>r=0..b+1. f_38 U V r (b+1-r))"
      by (auto simp add: f_38_def algebra_simps)

    have e3: "((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))))
        = (\<Sum>r=1..b. f_38 U V r (b+1-r)) + (\<Sum>r=0..b+1. f_38 U V r (b+1-r))"
      using e31 e32 e33 e34 e35 e36 e37 e310 by auto

    have e41: "(U*V)^2*(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-r-1))) = U^2*V^2*(\<Sum>r=0..b-1. f_38 U V r (b-r-1))"
      by (auto simp add: algebra_simps f_38_def)
    have e42: "... = (\<Sum>r=0..b-1. U^2*V^2*f_38 U V r (b-r-1))"
      using Groups_Big.semiring_0_class.sum_distrib_left by auto
    have "r\<le> b-1 \<Longrightarrow> (Suc(b-r-1) = b-r)" for r
      using t by auto
    then have "r\<le> b-1 \<Longrightarrow> U^2*V^2*f_38 U V r (b-r-1) = f_38 U V (r+1) (b-r)" for r
      by (simp add: U_sq_f V_sq_f ab_semigroup_mult_class.mult_ac(1))
    then have e43: "(\<Sum>r=0..b-1. U^2*V^2*f_38 U V r (b-r-1)) = (\<Sum>r=0..b-1. f_38 U V (r+1) (b-r))"
      by auto
    have "... = (\<Sum>r=1..b. f_38 U V r (b+1-r))"
      using chang_var3 t by auto

    then have e4: "(U*V)^2*(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-r-1))) 
        = (\<Sum>r=1..b. f_38 U V r (b+1-r))"
      using e41 e42 e43 by auto

    have "(((U^2+V^2)*(\<Sum>r=0..(b+1-1). (U^(2*r))*(V^(2*(b+1-1-r)))))
        - (U*V)^2*(\<Sum>r=0..b-1. U^(2*r)*V^(2*(b-1-r)))) = (\<Sum>r=0..b+1. f_38 U V r (b+1-r))"
      using e3 e4 by auto
    then have "((A*U*V)*(U*V)^(b+1-1)*\<psi> A (b+1) - ((U*V)^2*(U*V)^(b-1)*\<psi> A b)) mod (U^2 - A*U*V +V^2)
        = (\<Sum>r=0..b+1. f_38 U V r (b+1-r)) mod (U^2 - A*U*V + V^2)"
      using e2 by auto
    then have "(U * V) ^ (b + 2 - 1) * \<psi> A (b + 2) mod (U\<^sup>2 - A * U * V + V\<^sup>2)
        = (\<Sum>r=0..b+1. f_38 U V r (b+1-r)) mod (U^2 - A*U*V + V^2)"
      using e1 by auto
    then have "(U * V) ^ (b + 2 - 1) * \<psi> A (b + 2) mod (U\<^sup>2 - A * U * V + V\<^sup>2)
        = (\<Sum>r=0..b+1. U^(2*r)*V^(2*(b+1-r))) mod (U^2 - A*U*V + V^2)"
      using f_38_def by auto
    then show ?case by auto
  qed
  show ?thesis using f0[of B] assms by auto
qed

corollary lucas_diophantine_aux:
  fixes B::nat and A::int
  assumes "B>0"
  shows "2^(B-1)*\<psi> A B mod (2*A-5) = (\<Sum>r=0..B-1. 2^(2*r)) mod (2*A-5)"
proof -
  have f1: "2^(B-1)*\<psi> A B mod (5-2*A)= (\<Sum>r=0..B-1. 2^(2*r)) mod (5-2*A)"
    using lucas_exponential_diophantine[of B 2 1 A] assms by (auto simp add: algebra_simps)
  have f2: "a mod c = b mod c \<Longrightarrow> a mod (-c) = b mod (-c)" for a::int and b::int and c::int
    by (metis mod_minus_eq mod_minus_right)
    then show ?thesis  using f2[of "2^(B-1)*\<psi> A B" "(5-2*A)" "(\<Sum>r=0..B-1. 2^(2*r))"] f1 by auto
  qed

text \<open>Reciprocal implication of lemma 3.12\<close>

lemma lucas_diophantine_rec:
  fixes B::nat and A::int and W::int
  assumes "B>0 \<and> abs A > W^4 \<and> abs A > 2^(4*B) \<and> 3*W*\<psi> A B mod (2*A-5) = 2*(W^2-1) mod (2*A-5)"
  shows "W = 2^B"
proof -
  have "2^n \<ge> (1::int)" for n::nat
    by simp
have "B \<ge> 1"
      using assms by auto
    then have "4*B \<ge> 4"
      by auto
    then have "4*(B-1) + 4 = (4::nat)*B"
      by auto
    then have "2^(4*B) = 2^(4*(B-1))*(2::int)^4"
      using power_add[of "2::int" "4*(B-1)" 4] by auto
    then have "2^(4*B) \<ge> (2::int)^4" by simp
    then have "2^(4*B) \<ge> (16::int)" by simp
    then have A_grand: "abs A > 16" using assms by auto

  have W_not_0: "W \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (W \<noteq> 0)"
    then have "0 mod (2*A-5) = -2 mod (2*A-5)"
      using assms by fastforce
    then have "2*A-5 dvd -2"
      by (simp add: mod_eq_0_iff_dvd)
    then have "abs (2*A-5) \<le> 2"
      by (metis abs_numeral add_eq_0_iff dbl_def dbl_simps(3)
          dvd_imp_le_int one_neq_neg_one uminus_dvd_conv(2))
    then have "2* abs A - 5 \<le> 2"
      by auto
    then have a_max: "abs A \<le> 3"
      by auto
    then show False using a_max A_grand by auto
  qed
  then have abs_W_sup_1: "abs W \<ge> 1" by auto

  have "2^(B-1)*\<psi> A B mod (2*A-5) = (\<Sum>r=0..B-1. 2^(2*r)) mod (2*A-5)"
    using assms lucas_diophantine_aux by auto
  then have e1: "2^(B-1)*3*W*\<psi> A B mod (2*A-5) = 3*W*(\<Sum>r=0..B-1. 2^(2*r)) mod (2*A-5)"
    using mod_mult_cong[of "3*W" "2*A-5" "3*W" "2^(B-1)*\<psi> A B" "(\<Sum>r=0..B-1. 2^(2*r))"]
    by (auto simp add: algebra_simps)
  have "2^(B-1)*2*(W^2-1) mod (2*A-5) = 2^(B-1)*3*W*\<psi> A B mod (2*A-5)"
    using assms mod_mult_cong[of "2^(B-1)" "2*A-5" "2^(B-1)" "3*W*\<psi> A B" "2*(W^2-1)"]
    by (auto simp add: algebra_simps)
  then have e2: "3*W*(\<Sum>r=0..B-1. 2^(2*r)) mod (2*A-5) = 2^(B-1)*2*(W^2-1) mod (2*A-5)"
    using e1 by auto
  have somme_geo: "(3::int)*(\<Sum>r=0..n. 2^(2*r)) = 2^(2*(n+1)) - 1" for n
  proof (induction n)
  case 0
    then show ?case by auto
  next
  case (Suc n)
    then show ?case by auto
  qed
  have "3*W*(\<Sum>r=0..B-1. 2^(2*r)) = W*(2^(2*B)-1)"
    using assms somme_geo[of "B-1"] by auto
  then have "W*(2^(2*B)-1) mod (2*A-5) = 2^(B-1)*2*(W^2-1) mod (2*A-5)"
    using e2 by presburger
  then have "W*(2^(2*B)-1) mod (2*A-5) = 2^B*(W^2-1) mod (2*A-5)"
    using assms by (metis power_minus_mult)
  then have e3: "(W*(2^(2*B)-1) - 2^B*(W^2-1)) mod (2*A-5) = 0 mod (2*A-5)"
    using mod_diff_cong[of "2^B*(W^2-1)" "2*A-5" "W*(2^(2*B)-1)" "2^B*(W^2-1)" "2^B*(W^2-1)"]
    by auto
  then have "(2^B*(W^2-1) - W*(2^(2*B)-1)) mod (2*A-5) = 0 mod (2*A-5)"
    by presburger
  have e4: "2^B*(W^2-1) - W*(2^(2*B)-1) = (2^B*W+1)*(W-2^B)"
    by (auto simp add: algebra_simps power2_eq_square power_mult)

  have "2^(2*B)-1 \<ge> (0::int)"
    by auto
  then have i0: "abs (W*(2^(2*B)-1)) = abs W * (2^(2*B)-1)"
    by (simp add: abs_mult_pos)
  have i1: "... =  abs W *2^(2*B) - abs W"
    by (auto simp add: algebra_simps)
  have i2: "... = abs W * 2^B * 2^B - abs W"
    by (simp add: power_add[of 2 B B] mult_2)
  have i_plus: "(2::int)^B*2^B \<ge> 0 \<and> 2^B \<le> (max (2^B) (abs W)) \<and> abs W \<le> (max (2^B) (abs W))"
    by auto
  then have i3: "abs W * 2^B * 2^B \<le> (max (2^B) (abs W)) * 2^B * 2^B"
    by auto
  then have i4: "...\<le> (max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W))"
    by (auto simp add: mult_mono)
  then have i5: "abs (W*(2^(2*B)-1)) \<le> (max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W)) - abs W"
    using i0 i1 i2 i3 i4 by linarith 

  have h0: "2^B*(W^2-1) = 2^B*W^2 - 2^B"
    by (auto simp add: algebra_simps)
  have h1: "... = 2^B*(abs W)*(abs W) - 2^B"
    using power2_eq_square by simp
  have h_plus: "(abs W)*(abs W) \<ge> 0 \<and> 2^B \<le> (max (2^B) (abs W)) \<and> abs W \<le> (max (2^B) (abs W))
      \<and> 0 \<le> (max (2^B) (abs W))"
    by auto
  then have h2: "2^B*(abs W)*(abs W) \<le> (max (2^B) (abs W))*(abs W)*(abs W)"
    by (simp add: mult_right_mono)
  moreover have h3: "... \<le> (max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W))"
    by (simp add: mult_mono)
  then have h4: "2^B*(W^2-1) \<le> (max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W)) - 2^B"
    using h0 h1 h2 h3 by linarith

  have h51:  "(max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W)) = (max (2^B) (abs W))^3"
    by (simp add: h4 power3_eq_cube)
  have h52: "... = max ((2^B)^3) ((abs W)^3)"
    using h_plus by (smt (verit, del_insts) power_mono zero_le_power)
  have "... = max (2^(3*B)) ((abs W)^3)"
    by (simp add: mult.commute power_mult)
  then have h53: "(max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W)) = max (2^(3*B)) ((abs W)^3)"
    using h51 h52 by auto
  have "abs A > 2^(3*B+B) "
    using assms by (auto simp add: algebra_simps)
  then have "abs A > 2^(3*B) * 2^B"
    using power_add[of 2 "3*B" B] by (smt (verit, best))
  then have h54: "abs A > 2^(3*B)"
    by (smt (z3) \<open>2 ^ (3 * B + B) < \<bar>A\<bar>\<close> not_add_less1 power_less_imp_less_exp)
  have "abs A > (abs W)^4"
    using assms by auto
  then have "abs A > (abs W)^3 * abs W"
    using power_add[of "abs W" 3 1] by auto
  then have "abs A > (abs W)^3"
    using abs_W_sup_1
    by (smt (verit, del_insts) one_power2 power2_eq_square
        power3_eq_cube power_commuting_commutes power_less_power_Suc)
  then have h55: "max (2^(3*B)) ((abs W)^3) < abs A"
    using h54 by auto
  then have h5: "(max (2^B) (abs W))*(max (2^B) (abs W))*(max (2^B) (abs W)) < abs A"
    using h53 by auto

  then have h: "2^B*(W^2-1) < abs A - 2^B"
    using h4 h5 by auto
  moreover have i: "abs (W*(2^(2*B)-1)) < abs A - abs W"
    using i5 h5 by auto

have W_not_1: "abs W \<noteq> 1"
  proof (rule ccontr)
    assume "\<not> (abs W \<noteq> 1)"
    note t = this
    then have "2^B*(W^2-1) = 0"
      by (metis cancel_comm_monoid_add_class.diff_cancel mult.commute
          mult_zero_left power2_abs power_one)
    then have j1: "W*(2^(2*B)-1) mod (2*A-5) = 0 mod (2*A-5)"
      using e3 by auto
    have j_20:  "abs (W*(2^(2*B)-1)) < abs A -1"
      using t i by auto
    have "abs A -1 < abs (2*A -5)"
      using A_grand by auto
    then have j2: "abs (W*(2^(2*B)-1)) < abs (2*A-5)"
      using j_20 by auto
    then have j3: "W*(2^(2*B)-1) = 0"
      using j1
      by (smt (z3) \<open>(2 ^ B * (W\<^sup>2 - 1) - W * (2 ^ (2 * B) - 1)) mod (2 * A - 5) = 0 mod (2 * A - 5)\<close>
          \<open>2 ^ B * (W\<^sup>2 - 1) = 0\<close> mod_neg_neg_trivial mod_pos_pos_trivial)
    then have j4: "2^(2*B)-(1::int) = 0"
      using t
      by (smt (verit) \<open>16 \<le> 2 ^ (4 * B)\<close> mult_cancel_right1 no_zero_divisors num_double
          power2_eq_square power_mult power_mult_distrib power_mult_numeral)
    have "2*B \<ge> 2" using assms by auto
    then have "2^(2*B) -1 \<ge> (3::int)"
      by (smt (verit, ccfv_threshold) j4
          one_power2 power2_eq_iff_nonneg power2_less_eq_zero_iff power_increasing)
    then show False using j4
      by (metis \<open>1 \<le> B\<close> abs_numeral abs_square_eq_1 add.left_neutral diff_add_cancel
          numeral_One numeral_le_iff one_le_numeral power_abs power_even_eq power_increasing
          power_one_right semiring_norm(69))
  qed
  then have W_sup_2: "abs W \<ge> 2"
    using W_not_0 by auto
  then have "abs (W*(2^(2*B)-1)) < abs A - 2"
    using i by auto
  then have i_fin: "abs (W*(2^(2*B)-1)) \<le> abs A -3"
    by auto

  have "B\<ge>1" using assms by auto
  then have maj_2_B: "2^B \<ge> (2::int)"
    by (metis  one_le_numeral power_increasing power_one_right)
  then have h_fin: "2^B*(W^2-1) < abs A - 2"
    using h by auto

  have "2^B*(W^2-1) \<ge> 0"
    by (simp add: W_not_0)
  then have "abs (W*(2^(2*B)-1) - 2^B*(W^2-1)) \<le> abs (W*(2^(2*B)-1)) + 2^B*(W^2-1)"
    by auto
  then have "abs (W*(2^(2*B)-1) - 2^B*(W^2-1)) < 2*abs A -5"
    using i_fin h_fin by auto
  then have "W*(2^(2*B)-1) - 2^B*(W^2-1) = 0" using e3
    by (smt (verit) \<open>(2 ^ B * (W\<^sup>2 - 1) - W * (2 ^ (2 * B) - 1)) mod (2 * A - 5) = 0 mod (2 * A - 5)\<close>
        mod_neg_neg_trivial mod_pos_pos_trivial)

  then have k0: "(2^B*W+1)*(W-2^B) = 0" using e4 by auto
  have k1: "abs (2^B*W+1) \<ge> 2^B*abs W -1" by auto
  have "2^B*abs W -1 \<ge> 3" using W_sup_2 maj_2_B
    by (smt (verit, ccfv_SIG) \<open>(2 ^ B * W + 1) * (W - 2 ^ B) = 0\<close> \<open>0 \<le> 2 ^ B * (W\<^sup>2 - 1)\<close>
        h0 h1 mult_cancel_left1 mult_le_0_iff mult_right_mono one_power2 power2_sum)
  then have "abs (2^B*W+1) \<ge> 3" using k1 by auto
  then have "2^B*W+1 \<noteq> 0" by auto
  then have "W-2^B = 0" using k0 by auto
  then show ?thesis by auto
qed

end
