theory Bridge_Theorem_Imp
  imports HOL.Binomial
          "../MPoly_Utils/Poly_Extract"
          "../Lucas_Sequences/DFI_square_0"
          "../Lucas_Sequences/Lucas_Diophantine"
          "../Lucas_Sequences/Lemma_4_4"
begin

section \<open>The Bridge Theorem\<close>

subsection \<open>Constructing polynomials\<close>

context bridge_variables
begin

definition L :: "int \<Rightarrow> int \<Rightarrow> int"
  where "L l Y = l * Y"
definition U :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "U l X Y = 2 * X * L l Y"
definition V :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "V w g Y = 4 * w * g * Y"
definition A :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "A l w g Y X = U l X Y * (V w g Y + 1)"
definition B :: "int \<Rightarrow> int"
  where "B X = 2 * X + 1"
definition C :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "C l w h g Y X = B X + (A l w g Y X - 2) * h"
definition D :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "D l w h g Y X = ((A l w g Y X)\<^sup>2 - 4) * (C l w h g Y X)\<^sup>2 + 4"
definition E :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "E l w h x g Y X = (C l w h g Y X)\<^sup>2 * D l w h g Y X * x"
definition F :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "F l w h x g Y X = 4 * ((A l w g Y X)\<^sup>2 - 4) * (E l w h x g Y X)\<^sup>2 + 1"
definition G :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "G l w h x g Y X = 1 + C l w h g Y X * D l w h g Y X * F l w h x g Y X -
                           2 * (A l w g Y X + 2) * (A l w g Y X - 2)\<^sup>2 * (E l w h x g Y X)\<^sup>2"
definition H :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "H l w h x y g Y X = C l w h g Y X + B X * F l w h x g Y X + (2 * y - 1) *
                             C l w h g Y X * F l w h x g Y X"
definition I :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "I l w h x y g Y X = ((G l w h x g Y X)\<^sup>2 - 1) * (H l w h x y g Y X)\<^sup>2 + 1"
definition W :: "int \<Rightarrow> int \<Rightarrow> int"
  where "W w b = b * w"
definition K :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "K k l w g Y X = X + 1 + k * ((U l X Y)\<^sup>2 * V w g Y - 2)"
definition J :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "J k l w g Y X = K k l w g Y X"

definition S :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "S l w g Y X = 2 * A l w g Y X - 5"

definition T :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where 
  "T l w h g Y X b = 3 * (W w b) * (C l w h g Y X) - 2 * ((W w b)\<^sup>2 - 1)"

poly_extract L
poly_extract U
poly_extract V
poly_extract A
poly_extract B
poly_extract C
poly_extract D
poly_extract E
poly_extract F
poly_extract G
poly_extract H
poly_extract I
poly_extract W
poly_extract K
poly_extract S
poly_extract T 


definition d2a where "d2a l w h x y g Y X = is_square(D l w h g Y X * F l w h x g Y X
                          * I l w h x y g Y X)"
definition d2b where "d2b k l w x g Y X = is_square((U l X Y^4*V w g Y^2-4)*K k l w g Y X^2+4)"
definition d2c where 
  "d2c l w h b g Y X \<equiv> S l w g Y X dvd T l w h g Y X b"
definition d2d where "d2d b w X=(b*w=2^nat(B X))"
definition d2e where "d2e k l w h g Y X=((4*g*(C l w h g Y X)-4*g*(L l Y)*
                      (K k l w g Y X))^2<(K k l w g Y X)^2)"
definition d2f where "d2f k l w h g Y X=((2*(C l w h g Y X)-2*(L l Y)*
                      (K k l w g Y X))^2<(K k l w g Y X)^2)"

definition statement1 where 
  "statement1 b Y X \<equiv> is_power2 b
                    \<and> Y dvd int (2 * nat X choose nat X)"

definition statement2 where 
  "statement2 b Y X g = (\<exists>h k l w x y::int.(l*x\<noteq>0)\<and>(d2a l w h x y g Y X)\<and>
                            (d2b k l w x g Y X)\<and>(d2c l w h b g Y X)\<and>(d2f k l w h g Y X))"
definition statement2a where 
  "statement2a b Y X g = (\<exists>h k l w x y::int.(d2a l w h x y g Y X)\<and>
                            (d2b k l w x g Y X)\<and>(d2c l w h b g Y X)\<and>(d2e k l w h g Y X)
                            \<and> (h\<ge>b)\<and>(k\<ge>b)\<and>(l\<ge>b)\<and>(w\<ge>b)\<and>(x\<ge>b)\<and>(y\<ge>b))"

end

lemma min_power:
  fixes a::int and n::nat
  assumes "a \<ge> 3"
  shows "(a-1)^(n+2) \<ge> 3 + int n + (a-2)^2"
proof (induction n)
  case 0
  have "(a-1)^2 = 1 - 2*a + a^2" by (auto simp add: algebra_simps power2_eq_square)
  also have "... = 2*a - 3 + (a^2 - 4*a + 4)" by auto
  also have "... = 2*a - 3 + (a-2)^2" by (auto simp add: algebra_simps power2_eq_square)
  also have "... \<ge> 3 + (a-2)^2" using assms by auto
  finally show ?case using plus_nat.add_0 by presburger
next
  case (Suc n)
  note t = this
  have "(a-1)^(Suc n + 2) = (a-1)*(a-1)^(n+2)" by auto
  then have "(a-1)^(Suc n + 2) \<ge> 2*(a-1)^(n+2)" using assms by auto
  then have "(a-1)^(Suc n + 2) \<ge> (a-1)^(n+2) + (a-1)^(n+2)" by auto
  then have "(a-1)^(Suc n + 2) \<ge> 1 + (a-1)^(n+2)" using assms
    by (smt (verit) one_le_power power_one)
  then show ?case using t by auto
qed

lemma change_sum:
  fixes f::"int \<Rightarrow> int" and n::nat
  shows "(\<Sum>i\<le>n. (f (int i))) = sum (\<lambda>i. f i) (set[0..int n])"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note t = this
  have "(\<Sum>i\<le>Suc n. f (int i)) = (\<Sum>i\<le>n. f (int i)) + f (int (Suc n))" by auto
  hence "(\<Sum>i\<le>Suc n. f (int i)) = sum (\<lambda>i. f i) (set[0..int n]) + f (int (Suc n))"
    using t by auto
  hence first_eq: "(\<Sum>i\<le>Suc n. f (int i)) = sum (\<lambda>i. f i) (set[0..int n]) 
    + sum (\<lambda>i. f i) (set[int (Suc n)..int (Suc n)])"
    by auto
  have "(set[0..int n]) \<inter> (set[int (Suc n)..int (Suc n)]) = {} \<and>
    (set[0..int n]) \<union> (set[int (Suc n)..int (Suc n)]) = (set[0..int (Suc n)])"
    by auto
  hence "(\<Sum>i\<le>Suc n. f (int i)) = sum (\<lambda>i. f i) (set[0..int (Suc n)])"
    using first_eq by (metis List.finite_set sum.union_disjoint)
  then show ?case by simp
qed

lemma chang_var1:
  fixes f::"int \<Rightarrow> int" and n::nat
  shows "sum (\<lambda>i. f (i+1)) (set[0..int n]) = sum (\<lambda>i. f i) (set[1..int (Suc n)])"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note t = this
  have "(set[0..int n])\<inter>{int (Suc n)} = {} \<and> (set[0..int n])\<union>{int (Suc n)} = (set[0..int (Suc n)])
    \<and> finite {int (Suc n)} \<and> finite (set[0..int n])" by auto
  hence eq1: "sum (\<lambda>i. f (i+1)) (set[0..int (Suc n)]) = sum (\<lambda>i. f (i+1)) (set[0..int n])
    + f (int (Suc n) +1)"
    using sum.union_disjoint by (smt (z3) Int_Un_eq(3) Un_insert_right disjoint_insert(2) sum.insert_if)
  have "(set[1..int (Suc n)])\<inter>{int (Suc (Suc n))} = {} \<and> (set[1..int (Suc n)])\<union>{int (Suc (Suc n))} 
    = (set[1..int (Suc (Suc n))]) \<and> finite {int (Suc (Suc n))} \<and> finite (set[1..int (Suc n)])"
    by auto
  hence "sum (\<lambda>i. f i) (set[1..int (Suc (Suc n))]) = sum (\<lambda>i. f i) (set[1..int (Suc n)])
    + f (int (Suc n) + 1)"
    using sum.union_disjoint[of "(set[1..int (Suc n)])" "{int (Suc (Suc n))}" f] by auto
    then show ?case using t eq1 by auto
qed

lemma chang_var:
  fixes f::"int \<Rightarrow> int" and n::nat and m::nat
  shows "sum (\<lambda>i. f i) (set[int n..int (n+m)]) = sum (\<lambda>i. f (int (n+m) - i)) (set[0..int m])"
proof (induction m)
case 0
  then show ?case by auto
next
  case (Suc m)
  note t = this
  have "(set[int n..int (n+m)])\<inter>(set[int (n+Suc m)..int (n+Suc m)]) = {}
    \<and> (set[int n..int (n+m)])\<union>(set[int (n+Suc m)..int (n+Suc m)]) = (set[int n..int (n+Suc m)])
    \<and> finite (set[int n..int (n+m)]) \<and> finite (set[int (n+Suc m)..int (n+Suc m)])" by auto
  hence "sum (\<lambda>i. f i) (set[int n..int (n+Suc m)]) = sum (\<lambda>i. f i) (set[int n..int (n+m)]) 
    + f (int (n + Suc m))"
    using sum.union_disjoint[of "(set[int n..int (n+m)])" "(set[int (n + Suc m)..int (n+Suc m)])" f]
    by auto
  hence eq1: "sum (\<lambda>i. f i) (set[int n..int (n+Suc m)]) = sum (\<lambda>i. f (int (n+m) - i)) (set[0..int m])
     + f (int (n + Suc m))"
    using t by auto
  have "int (n+ Suc m) - (i+1) = int (n+m) - i" for i by auto
  hence "sum (\<lambda>i. f (int (n+m) - i)) (set[0..int m]) = sum (\<lambda>i. f (int (n+Suc m) - (i+1))) (set[0..int m])"
    by presburger
  hence eq2: "sum (\<lambda>i. f i) (set[int n..int (n+Suc m)]) = 
    sum (\<lambda>i. f (int (n+Suc m) - (i+1))) (set[0..int m]) + f (int (n + Suc m))"
    using eq1 by presburger
  define g::"int\<Rightarrow>int" where "g i = f (int (n + Suc m) - i)" for i
  hence "sum (\<lambda>i. f i) (set[int n..int (n+Suc m)]) = sum (\<lambda>i. g (i+1)) (set[0..int m]) + g 0"
    using eq2 by auto
  hence eq3: "sum (\<lambda>i. f i) (set[int n..int (n+Suc m)]) = sum (\<lambda>i. g i) (set[1..int (Suc m)]) + g 0"
    using chang_var1[of g m] by auto
  have "(set[1..int (Suc m)])\<union>{0} = (set[0..int (Suc m)]) \<and> (set[1..int (Suc m)])\<inter>{0} = {}
    \<and> finite (set[1..int (Suc m)]) \<and> finite {0}" by auto
  hence "sum (\<lambda>i. f i) (set[int n..int (n+Suc m)]) = sum (\<lambda>i. g i) (set[0..int (Suc m)])"
    using eq3 sum.union_disjoint[of "{0}" "(set[int n..int (n+Suc m)])" g]
    by (smt (verit) Int_empty_right finite_insert insert_disjoint(2) sum.insert sum_Un)
  then show ?case using g_def by auto
qed

subsection \<open>Proof of implication \<open>(1)\<Longrightarrow>(3)\<close>\<close>

context bridge_variables
begin

lemma theorem_II_1_3:
  assumes b_def1:"(b::int)\<ge>0" and Y_def:"(Y::int)\<ge>b\<and>Y\<ge>2^8" and X_def:"(X::int)\<ge>3*b"
          and g_def:"(g::int)\<ge>1"
  shows "(statement1 b Y X) \<Longrightarrow> (statement2a b Y X g)"
proof -
    assume state1:"statement1 b Y X"
    hence b_def: "b \<ge> 1" unfolding statement1_def is_power2_def 
      using b_def1 by force

    hence X_pos: "X > 0" using assms by auto
      
    define w where w_def:"w=(2^nat(B X))div b"
    have is_power2_b:"is_power2 b" using state1 and statement1_def by auto
    have is_power2B_b_bsq:"2^nat (B X) > b^2"
    proof -
      have obvious_natX: "nat (2*X+1) = 1+2*nat X" using X_pos by auto
      have pow_2_useful: "(2::int)^(2*n+1) = 2*(2^n)^2" for n
      proof (induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        then show ?case by (auto simp add: algebra_simps)
      qed
      have "2^n \<ge> int n" for n
      proof (induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        note t = this
        have "(2::int)^(Suc n) - 2^n = 2^n" by auto
        then have "(2::int)^(Suc n) - 2^n \<ge> 1" by auto
        then have "(2::int)^(Suc n) \<ge> 2^n + 1" by auto
        then have "(2::int)^(Suc n) \<ge> int n + 1" using t by linarith
        then show ?case by auto
      qed
      hence pow_2_bigger: "((2::int)^n)^2\<ge> (int n)^2" for n by auto
      have "(2::int)^nat(B X) = 2^nat(2*X+1)"
        by (simp add: B_def)
      then have "(2::int)^nat (B X) = 2^(1+2*nat X)"
        using obvious_natX by simp
      hence "(2::int)^nat (B X) = 2*(2^nat X)^2"
        using pow_2_useful by auto
      hence "(2::int)^nat(B X) > (2^nat X)^2" by auto
        hence "2^nat(B X) > (int (nat X))^2" using pow_2_bigger[of "nat X"] by linarith
        hence "2^nat (B X) > X^2" using X_pos by auto
        thus ?thesis using X_def b_def
          by (smt (verit, best) power2_less_imp_less)
    qed
    have is_power2B_b_b:"2^nat (B X) > b"
    proof -
      show ?thesis using b_def and is_power2B_b_bsq
        by (smt (verit, ccfv_threshold) self_le_power zero_less_numeral)
    qed 

    text \<open> Proof of d2d and \<open>w\<ge>b\<close>\<close>

    have "\<exists>k. b = 2^k" using is_power2_b unfolding is_power2_def 
      by (simp add: b_def1)

    then obtain k where k_def: "b=2^k" by auto
    then have "k < nat(B X)" using is_power2B_b_b by auto
    hence "w = 2^(nat(B X) - k)" using k_def w_def
      by (simp add: \<open>k < nat (B X)\<close> less_imp_le_nat power_diff_power_eq)
    hence sat_4_2d:"d2d b w X" using k_def unfolding d2d_def    
        by (metis Nat.add_diff_assoc \<open>k < nat (B X)\<close> add_diff_cancel_left' less_imp_le_nat power_add)
    have wBeb:"w\<ge>b"
    proof -
      have "w*b>b^2" using sat_4_2d is_power2B_b_bsq d2d_def by (metis mult.commute)
      hence "w*b>b*b" by (simp add: power2_eq_square)
      thus ?thesis using b_def by auto
    qed

    have "b \<ge> 1" using is_power2_b using b_def by auto
    hence VBe1: "V w g Y \<ge> 1" unfolding V_def using assms wBeb mult_mono[of 1 w 1 "g*Y"] 
      mult_mono[of 1 g 1 Y] by auto

    text \<open> Introduction of \<open>\<rho>\<close> \<close>

    define \<rho>_int where pI_def:"\<rho>_int = ((2*nat X) choose nat X) + nat((V w g Y)*sum 
      (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X]))"


    define l where l_def:"l=int \<rho>_int div Y"  
    have "\<rho>_int \<ge> nat((V w g Y)*sum 
      (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X]))"
      using pI_def by auto
    then have \<rho>_int_min1: "int \<rho>_int \<ge> (V w g Y)*sum 
      (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X])" by auto
    have V_pos: "V w g Y >0" unfolding V_def using assms wBeb b_def by force
    hence V_pos2: "(V w g Y)^(nat i) \<ge>1 " for i by auto
    have binom_pos: "int (2*nat X choose nat i) \<ge> 0" for i by auto
    have binom_strict_pos: "\<And>i. i\<in>set[X+1..2*X] \<Longrightarrow> int (2*nat X choose nat i) > 0"
    proof -
      fix i::int
      assume i_def: "i\<in>set[X+1..2*X]"
      show "int (2*nat X choose nat i) > 0" using zero_less_binomial[of "nat i" "2*nat X"] i_def  
        by auto
    qed
    have min_binom1: "int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1) 
\<ge> int (2*nat X choose nat i)" for i 
      using V_pos2[of "i-X-1"] binom_pos[of i] by (simp add: mult_le_cancel_left1)
    hence terms_pos: "\<And>i. i\<in>set[X+1..2*X] \<Longrightarrow> int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1) > 0"
      using binom_strict_pos by (smt (z3))
    define enof::"int\<Rightarrow>int" where "\<And>i. enof i = int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)"
    have "set[X+1..2*X] \<noteq> {} \<and> finite (set[X+1..2*X])" using X_pos by auto
    hence sum_pos: "sum (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X]) > 0" 
      using terms_pos Groups_Big.ordered_comm_monoid_add_class.sum_pos[of "set[X+1..2*X]" enof]
 enof_def by auto
    have lBeb:"l\<ge>b"
    proof -
      have "sum (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X]) \<ge> 1" 
        using sum_pos by auto
      hence "V w g Y * (\<Sum>i\<in>set [X + 1..2 * X]. int (2*nat X choose nat i) * 
        V w g Y ^ nat (i - X - 1)) \<ge> V w g Y" using V_pos by auto
      hence "int \<rho>_int\<ge>V w g Y" using \<rho>_int_min1 by auto
      hence "l\<ge>(V w g Y)div Y" using l_def using Y_def zdiv_mono1 by auto
      hence "l\<ge>4*g*w" using V_def
        by (smt (verit, ccfv_threshold) Y_def b_def int_distrib(1) 
          mult.commute nonzero_mult_div_cancel_right)
      hence "l\<ge>w" using g_def by (smt (verit) b_def mult_le_cancel_right1 wBeb)
      thus ?thesis using wBeb by auto
    qed

    text \<open> Introduction of h \<close>

    define h where "h = (\<psi> (A l w g Y X) (nat(B X)) - B X) div (A l w g Y X - 2)"
    have UBe2:"U l X Y\<ge>2" using U_def lBeb Y_def X_def b_def
      by (smt (verit, ccfv_SIG) L_def b_def mult_le_cancel_left1)
    have A_Be_2Vp1:"A l w g Y X \<ge> 2 * (V w g Y + 1)"
    proof -
      have "V w g Y + 1 \<ge>0" using VBe1 by simp
      hence maj1: "U l X Y * (V w g Y + 1) \<ge> 2 * (V w g Y + 1)"
        using UBe2 Rings.ordered_semiring_class.mult_right_mono[of 2 "U l X Y" "V w g Y + 1" ] 
        by simp
      have "A l w g Y X = U l X Y * (V w g Y + 1)" using A_def by auto
      thus ?thesis using maj1 by simp
    qed
    have ABe4:"A l w g Y X \<ge> 4"
    proof -
      show ?thesis using VBe1 A_Be_2Vp1 by auto 
    qed
    have VBw:"V w g Y > w"
    proof -
      have "V w g Y=4*g*Y*w" using V_def by auto
      thus ?thesis using Y_def g_def wBeb b_def 
        by (smt (verit, best) mult_cancel_right1 mult_le_cancel_right1)
    qed 
    have BBe3: "nat(B X) \<ge> 3" unfolding B_def using assms b_def by auto
    have h_def2:"\<psi> (A l w g Y X) (nat(B X)) = B X + (A l w g Y X - 2)*h"
    proof -
      have "\<psi> (A l w g Y X) (nat(B X)) mod (A l w g Y X - 2) =  B X mod (A l w g Y X - 2)"
        using BBe3 lucas_congruence2[of "A l w g Y X" "nat (B X)"] ABe4 by simp
      hence "(\<psi> (A l w g Y X) (nat(B X)) - B X) mod (A l w g Y X - 2) = 0"
        using ABe4 mod_diff_eq
[of "(\<psi> (A l w g Y X) (nat(B X)))" "A l w g Y X - 2" "B X" ]
        by simp
      thus ?thesis using h_def by auto
    qed
    have hBeb:"h\<ge>b"
    proof -
      have "\<psi> (A l w g Y X) (nat (B X)) \<ge> B X + (A l w g Y X - 2)^2"
      proof -
        have BBe3: "B X \<ge> 3" using X_pos B_def by (smt (verit, ccfv_threshold))
        have some_trivial_facts: "nat (B X) - 3 + 2 = nat (B X) - 1 \<and> 3 + int (nat (B X) - 3) = B X"
          using BBe3 by auto
        have "Suc (Suc (nat (B X) - 2)) = nat (B X) \<and> nat (B X) - 2 + 1 = nat (B X) - 1" 
          using BBe3 by auto
        hence "\<psi> (A l w g Y X) (nat (B X)) \<ge> (A l w g Y X - 1) ^(nat (B X) - 1)"
          using lucas_exp_growth_gt[of "A l w g Y X" "nat (B X)-2"] ABe4 by auto
        hence "\<psi> (A l w g Y X) (nat (B X)) \<ge> B X + (A l w g Y X-2)^2"
          using min_power[of "A l w g Y X" "nat (B X) - 3"] BBe3 ABe4 some_trivial_facts by fastforce
        then show ?thesis by simp
      qed
      hence "B X + (A l w g Y X - 2)*h \<ge> B X + (A l w g Y X - 2)^2"
        using h_def2 by auto
      hence "(A l w g Y X - 2)*h \<ge> (A l w g Y X - 2)^2" by auto
      hence "h\<ge>A l w g Y X - 2" using ABe4 power2_eq_square[of "A l w g Y X - 2"] by auto
      hence "h\<ge>2*V w g Y" using A_Be_2Vp1 by auto
      hence "h\<ge>w" using VBw VBe1 by auto
      thus ?thesis using wBeb by auto
    qed

    text \<open> Introduction of x y and d2a \<close>

    define A_g where "A_g = A l w g Y X"
    define B_g where "B_g = B X"
    define C_g where "C_g = \<psi> A_g (nat B_g)"
    have C_well_def: "C_g = C l w h g Y X"unfolding C_g_def C_def A_g_def B_g_def 
      using h_def2 by simp
    then have D_well_def: "D l w h g Y X = D_f A_g C_g" unfolding D_def D_f_def A_g_def by simp
    then have E_well_def: "E l w h x g Y X = E_ACx A_g C_g x" for x
      unfolding E_def E_ACx_def E_f_def A_g_def using C_well_def by simp
    have F_well_def: "F l w h x g Y X = F_ACx A_g C_g x" for x
      unfolding F_def F_ACx_def F_f_def  using C_well_def E_well_def[of x] D_well_def A_g_def 
      by simp
    have G_well_def: "G l w h x g Y X = G_ACx A_g C_g x" for x
      unfolding G_def G_ACx_def G_f_def using D_well_def E_well_def[of x] F_well_def[of x]
      C_well_def A_g_def by simp
    have H_well_def: "H l w h x y g Y X = H_ABCxy A_g B_g C_g x y" for x y
      unfolding H_def H_ABCxy_def H_f_def B_g_def using C_well_def F_well_def[of x] by simp
    have I_well_def: "I l w h x y g Y X = I_ABCxy A_g B_g C_g x y" for x y
      unfolding I_def I_ABCxy_def I_f_def using G_well_def[of x] H_well_def[of x y] by auto
    have conditions_req: "A_g \<ge> 4 \<and> even A_g \<and> B_g \<ge> 3"
      unfolding A_g_def B_g_def B_def using ABe4 X_pos A_def U_def by auto
    have "\<exists>x\<ge>b. \<exists>y\<ge>b. d2a l w h x y g Y X"
      unfolding d2a_def using lemma_4_2_cor[of A_g B_g]
      by (simp add: C_g_def D_well_def F_well_def I_well_def lemma_4_2_cor[of A_g B_g]
      conditions_req is_square_def)
    then obtain x y where sat_4_2a:"x \<ge> b \<and> y \<ge> b \<and> d2a l w h x y g Y X" by auto

    text \<open> Introduction of k \<close>

    have X_plus_1Be2: "nat X + 1 \<ge> 2" using X_pos by auto
    hence intnatX: "int (nat X +1) = X + 1" by auto
    have V_pos: "V w g Y > 0" unfolding V_def using assms wBeb b_def by force
    hence U2VBe3: "U l X Y ^2 * V w g Y \<ge> 3" using UBe2 power2_eq_square
      by (smt (verit, ccfv_SIG) VBw b_def mult_cancel_right2 mult_less_cancel_right2 wBeb)
    hence "\<psi> (U l X Y ^2*V w g Y) (nat X + 1) mod (U l X Y ^2*V w g Y-2) 
      = int (nat X+1) mod (U l X Y ^2*V w g Y-2)"
      using lucas_congruence2[of "U l X Y ^2 * V w g Y" "nat X + 1"] X_plus_1Be2  by auto
    hence "\<psi> (U l X Y ^2*V w g Y) (nat X + 1) mod (U l X Y ^2*V w g Y-2) 
      = (X+1) mod (U l X Y ^2*V w g Y-2)"
      using intnatX by presburger
    then obtain k where k_def: "\<psi> ((U l X Y)^2*V w g Y) (nat X + 1)=X+1+((U l X Y)^2*V w g Y-2)*k"
      by (metis mod_eqE)
    have kBeb:"k\<ge>b"
    proof -
      have weird_eq: "nat X - 2 + 2 = nat X \<and> 3+int (nat X - 2) = X +1" using assms b_def by auto
      have "Suc (Suc (nat X -1)) = nat X +1 \<and> nat X - 1 + 1 = nat X" using X_pos by auto
      hence "\<psi> ((U l X Y)^2*V w g Y) (nat X +1)\<ge>((U l X Y)^2*V w g Y-1)^nat X"
        using lucas_exp_growth_gt[of "(U l X Y)^2*V w g Y" "nat X-1"] U2VBe3 by auto
      hence "\<psi> ((U l X Y)^2*V w g Y) (nat X +1)\<ge>1+X+((U l X Y)^2*V w g Y-2)^2" 
        using min_power[of "(U l X Y)^2*V w g Y" "nat X - 2"] weird_eq U2VBe3
        by (smt (verit, del_insts))
      hence "X+1+((U l X Y)^2*V w g Y-2)*k\<ge>1+X+((U l X Y)^2*V w g Y-2)^2" using k_def by auto
      hence "((U l X Y)^2*V w g Y-2)*k\<ge>((U l X Y)^2*V w g Y-2)^2" by auto
      hence "((U l X Y)^2*V w g Y-2)*k\<ge>((U l X Y)^2*V w g Y-2)*((U l X Y)^2*V w g Y-2)"
        by (simp add: power2_eq_square)
      hence ineq1: "k\<ge>((U l X Y)^2*V w g Y-2)" using UBe2 VBe1
        by (smt (verit, best) mult_le_cancel_left1 mult_le_cancel_left_pos one_power2 power2_diff)
      have U2Be4: "U l X Y ^2\<ge> 4" using UBe2 power2_eq_square[of "U l X Y"]
        by (smt (verit, best) dbl_simps(3) dbl_simps(5) numeral_eq_one_iff numeral_times_numeral
          one_power2 power2_le_imp_le power2_sum semiring_norm(11))
      hence "(U l X Y)^2*V w g Y-2 >= 4*V w g Y - 2" using V_pos by auto
      hence ineq2: "k \<ge> 4*V w g Y - 2" using ineq1 by auto
      have VBeb:"V w g Y\<ge>b" using wBeb g_def Y_def V_def VBe1
        by (smt (verit) mult_le_cancel_right1)
      hence "k \<ge> 4*b - 2" using ineq2 by auto
      hence "k \<ge> b + 1" using assms b_def by auto
      thus ?thesis by auto
    qed

    text \<open> Proof of d2b \<close>

    have sat_4_d2b: "d2b k l w x g Y X" unfolding d2b_def is_square_def
    proof -
      have 0: "U l X Y ^ 4 * (V w g Y)\<^sup>2 = (U l X Y ^ 2 * (V w g Y))^2" by algebra
      have "X + 1 + k * ((U l X Y)\<^sup>2 * V w g Y - 2) = \<psi> ((U l X Y)\<^sup>2 * V w g Y) (nat X+1)"
        using k_def by simp
      thus "\<exists>m. (U l X Y ^ 4 * (V w g Y)^2 - 4) * (K k l w g Y X)\<^sup>2 + 4 = m\<^sup>2"
        using lucas_pell_part2[of "K k l w g Y X" "U l X Y ^2*V w g Y"] K_def 0 by auto
    qed

    text \<open> Proof of d2c \<close>

    have sat_4_d2c: "d2c l w h b g Y X"
    proof -
      have A_pos:"0 < A l w g Y X" unfolding A_def using UBe2 VBe1 by simp
      have B_pos: "B X \<ge> 0" using assms unfolding B_def by force
      have hmm: "((2::int) ^ (nat (B X))) ^ 2 = (2::int) ^ (nat (B X) * 2)"
        using Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(31)
          [of 2 "nat(B X)" 2] by fast
      hence W2: "(W w b)\<^sup>2 = (2::int) ^ (2 * nat (B X))" using sat_4_2d unfolding d2d_def W_def
        by force
      have C_psi: "\<psi> (A l w g Y X) (nat (B X)) = C l w h g Y X" using C_g_def C_well_def A_g_def 
        B_g_def by fast
      have "3 * 2 ^ nat (B X) * \<psi> (A l w g Y X) (nat (B X)) mod (2 * A l w g Y X - 5) 
        = 2 * (2 ^ (2 * nat (B X)) - 1) mod (2 * A l w g Y X - 5)"
        using sat_4_2d unfolding W_def d2d_def
        using lucas_diophantine_dir[of "nat (B X)" "A l w g Y X"] by force
      hence "3 * W w b * C l w h g Y X mod (2 * A l w g Y X - 5) = 2 * ((W w b)\<^sup>2 - 1) 
        mod (2 * A l w g Y X - 5)" using sat_4_2d C_psi W2 unfolding W_def d2d_def by auto
      then have "(3 * W w b * C l w h g Y X - 2 * ((W w b)\<^sup>2 - 1)) mod (2 * A l w g Y X - 5) = 0"
        using mod_diff_cong by fastforce
      hence goal: "2 * A l w g Y X - 5 dvd 3 * W w b * C l w h g Y X - 2 * ((W w b)\<^sup>2 - 1)" by force
      show "d2c l w h b g Y X" 
        using goal unfolding S_def[symmetric] T_def[symmetric] d2c_def by auto
    qed

    (* Proof of d2e *)

    have "V w g Y \<le> V w g Y * (\<Sum>i\<in>set [X + 1..2 * X]. int (2 * nat X choose nat i)
      * V w g Y ^ nat (i - X - 1))" using sum_pos V_pos by auto
    hence \<rho>_int_min2: "int \<rho>_int \<ge> V w g Y" using \<rho>_int_min1 by auto
    have l_def2: "int \<rho>_int = l*Y"
    proof -
      have eq1: "int \<rho>_int = int ((2*nat X) choose nat X) + int(nat((V w g Y)*sum 
        (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X])))"
        using pI_def by auto
      hence int_sum: "int \<rho>_int = int ((2*nat X) choose nat X) + V w g Y * sum 
        (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^nat (i-X-1)) (set[X+1..2*X])"
        using V_pos sum_pos by auto
      have div_binom: "int ((2*nat X) choose nat X) mod Y = 0 mod Y" 
        using state1 statement1_def[of b Y X]
        by presburger
      have "V w g Y mod Y = 0 mod Y" unfolding V_def by auto
      hence "int \<rho>_int mod Y = 0 mod Y" using int_sum div_binom by auto
      then show ?thesis using l_def by auto
    qed

    have "(U l X Y)^2*V w g Y \<ge> U l X Y ^2" using V_pos mult_le_cancel_left1 by fastforce
    hence "(U l X Y)^2*V w g Y \<ge> U l X Y" using power2_eq_square[of "U l X Y"]
        mult_le_cancel_left1[of "U l X Y" "U l X Y"] by (auto simp add: UBe2)
    hence "U l X Y ^2 * V w g Y \<ge> 2 * X * L l Y" using U_def by auto
    hence "U l X Y ^2 * V w g Y \<ge> 2 * X * int \<rho>_int" using L_def l_def2 by auto
    hence "U l X Y ^2 * V w g Y \<ge> 2 * X * V w g Y" using \<rho>_int_min2 X_pos
      by (smt (z3) mult_left_mono)
    hence U2VBe2X: "U l X Y ^2 * V w g Y \<ge> 2*X" using V_pos X_pos mult_left_mono[of 1 "2*X" "V w g Y"]
      using \<open>(U l X Y)\<^sup>2 \<le> (U l X Y)\<^sup>2 * V w g Y\<close> by auto
    hence U2VBe2: "U l X Y ^2 * V w g Y > 1" using X_pos by auto

    define \<rho>_frac where "\<rho>_frac = sum (\<lambda>i. int (2*nat X choose nat i) * (V w g Y)^(nat i)) (set[0..X-1])"
    have decomp_of_p: "(V w g Y)^nat X*int \<rho>_int + \<rho>_frac = (V w g Y +1)^(2*nat X)"
    proof -
      have binom_eq1: "(V w g Y+1)^(2*nat X) = (\<Sum>i\<le>2*nat X. int (2*nat X choose i) * (V w g Y)^i)"
        using binomial_ring[of "V w g Y" 1 "2*nat X"] by auto
      define new_function::"int \<Rightarrow> int" where 
         "new_function i = int (2*nat X choose nat i) * (V w g Y)^(nat i)" for i
      hence "(V w g Y+1)^(2*nat X) = (\<Sum>i\<le>2*nat X. new_function (int i))" using binom_eq1 by auto
      hence binom_eq2: "(V w g Y+1)^(2*nat X) = sum (\<lambda>i. new_function i) (set[0..2*X])"
        using X_pos change_sum[of new_function "2*nat X"] by auto
      have "(set[0..2*X]) = (set[0..X-1])\<union>(set[X..2*X]) \<and> (set[0..X-1])\<inter>(set[X..2*X]) = {} 
        \<and> finite (set[0..X-1]) \<and> finite (set[X..2*X])" by auto
      hence binom_eq3: "(V w g Y+1)^(2*nat X) = \<rho>_frac + sum (\<lambda>i. new_function i) (set[X..2*X])"
        using binom_eq2 \<rho>_frac_def sum.union_disjoint[of "(set[0..X-1])" "(set[X..2*X])"
          new_function] by (metis (mono_tags, lifting) \<open>new_function 
          \<equiv> \<lambda>i. int (2 * nat X choose nat i) * V w g Y ^ nat i\<close> sum.cong)
      have "(set[X..2*X]) = {X}\<union>(set[X+1..2*X]) \<and> {X}\<inter>(set[X+1..2*X]) = {} \<and> finite {X}
        \<and> finite (set[X+1..2*X])" using assms by auto
      hence "sum (\<lambda>i. new_function i) (set[X..2*X]) = new_function X 
        + sum (\<lambda>i. new_function i) (set[X+1..2*X])"
        using sum.union_disjoint[of "{X}" "(set[X+1..2*X])" new_function] by auto
      hence binom_eq4: "(V w g Y+1)^(2*nat X) = \<rho>_frac + int (2*nat X choose nat X)*(V w g Y)^nat X 
        + sum (\<lambda>i. new_function i) (set[X+1..2*X])"
        using binom_eq3 new_function_def by auto
      define other_func::"int\<Rightarrow>int" where
        "other_func i = int (2*nat X choose nat i) * (V w g Y)^(nat (i-X-1))" for i
      have "\<And>i. i\<in>(set[X+1..2*X]) \<Longrightarrow> (V w g Y)^(nat i) = (V w g Y)^(nat X + 1)*(V w g Y)^nat (i-X-1)"
      proof -
        fix i
        assume "i\<in>(set[X+1..2*X])"
        hence "nat X +1 + nat (i-X-1) = nat i" by auto
        thus "(V w g Y)^(nat i) = (V w g Y)^(nat X + 1)*(V w g Y)^nat (i-X-1)"
          using power_add[of "V w g Y" "nat X +1" "nat (i-X-1)"]  by auto
      qed
      hence "\<And>i. i\<in>(set[X+1..2*X]) \<Longrightarrow> new_function i = (V w g Y)^(nat X + 1)*
        (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1))" using new_function_def by auto
      hence "sum (\<lambda>i. new_function i) (set[X+1..2*X]) = 
        sum (\<lambda>i. (V w g Y)^(nat X +1)* (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1))) 
        (set[X+1..2*X])" by auto
      hence  "sum (\<lambda>i. new_function i) (set[X+1..2*X]) = 
        sum (\<lambda>i. (V w g Y)^(nat X+1)*other_func i) (set[X+1..2*X])"
        using other_func_def by auto
      hence "sum (\<lambda>i. new_function i) (set[X+1..2*X]) = (V w g Y)^(nat X +1)*
        sum (\<lambda>i. (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1))) (set[X+1..2*X])"
        using sum_distrib_left[of "(V w g Y)^(nat X +1)" other_func "(set[X+1..2*X])"] other_func_def
        by auto
      hence "sum (\<lambda>i. new_function i) (set[X+1..2*X]) = (V w g Y)^nat X*(V w g Y*
        sum (\<lambda>i. (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1))) (set[X+1..2*X]))"
        using power_Suc[of "V w g Y" "nat X"] by auto
      hence "(V w g Y+1)^(2*nat X) = \<rho>_frac + int (2*nat X choose nat X)*(V w g Y)^nat X 
        + (V w g Y)^nat X*(V w g Y* sum (\<lambda>i. (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1)))
        (set[X+1..2*X]))"
        using binom_eq4 by auto
      hence binom_eq5: "(V w g Y+1)^(2*nat X) = \<rho>_frac + (V w g Y)^nat X * (int (2*nat X choose nat X)
        + (V w g Y* sum (\<lambda>i. (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1))) (set[X+1..2*X])))"
        by (auto simp add: algebra_simps)
      have "int \<rho>_int = int (2*nat X choose nat X) +
        (V w g Y* sum (\<lambda>i. (int (2*nat X choose nat i)*(V w g Y)^nat (i-X-1))) (set[X+1..2*X]))"
        using pI_def VBw \<open>V w g Y \<le> V w g Y * (\<Sum>i\<in>set [X + 1..2 * X]. int (2 * nat X choose
        nat i) * V w g Y ^ nat (i - X - 1))\<close> b_def wBeb by linarith
      thus ?thesis using binom_eq5 by auto
    qed

    have \<rho>_frac_pos: "\<rho>_frac \<ge> 0"
    proof -
      define q::"int\<Rightarrow>int" where "q i = int (2*nat X choose nat i) * (V w g Y)^(nat i)" for i
      have "int (2*nat X choose nat i) \<ge> 0 \<and> (V w g Y)^(nat i) \<ge> 0" for i
        using V_pos by auto
      hence q_pos: "q i \<ge> 0" for i
        using q_def by auto
      have "\<rho>_frac = sum (\<lambda>i. q i) (set[0..X-1])" unfolding \<rho>_frac_def q_def by auto
      thus ?thesis using q_pos by (simp add: sum_nonneg)
    qed

    have \<rho>_frac_L_inv8g: "8*g*\<rho>_frac < (V w g Y)^nat X"
    proof -
      define f1::"int \<Rightarrow> int" where "f1 i = int (2*nat X choose nat i) *(V w g Y)^(nat i)" for i
      define f2::"int \<Rightarrow> int" where "f2 i = int (2*nat X choose nat i) *(V w g Y)^(nat (X-1))" for i
      define f3::"int \<Rightarrow> int" where "f3 i = int (2*nat X choose nat i)" for i
      have "i\<in>(set[0..X-1]) \<Longrightarrow> (V w g Y)^(nat i) \<le> (V w g Y)^(nat (X-1))" for i
      proof -
        fix i
        assume i_def: "i\<in>(set[0..X-1])"
        have "nat i \<le> nat (X-1)" using i_def by auto
        thus "(V w g Y)^(nat i) \<le> (V w g Y)^(nat (X-1))" by (simp add: VBe1 power_increasing)
      qed
      hence "i\<in>(set[0..X-1]) \<Longrightarrow> f1 i \<le> f2 i" for i using f1_def f2_def mult_left_mono 
        by (metis binom_pos)
      hence "sum (\<lambda>i. f1 i) (set[0..X-1]) \<le> sum (\<lambda>i. f2 i) (set[0..X-1])" 
        using sum_mono[of "(set[0..X-1])" f1 f2] by auto
        hence "\<rho>_frac \<le> sum (\<lambda>i. int (2*nat X choose nat i) *(V w g Y)^(nat (X-1))) (set[0..X-1])"
      using \<rho>_frac_def f1_def f2_def by auto
    hence ineq_pfrac_1: "\<rho>_frac \<le> sum (\<lambda>i. int (2*nat X choose nat i) ) 
      (set[0..X-1]) *(V w g Y)^(nat (X-1))"
      using sum_distrib_right[of f3 "(set[0..X-1])" "(V w g Y)^(nat (X-1))"] f3_def by auto
    have ineq_binom: "k<n \<Longrightarrow> (\<Sum>i\<le>k. n choose i) < 2^n" for k::nat and n::nat
    proof -
      define f where "f i = n choose i" for i
      assume kn_def: "k < n"
      have eq_1: "(\<Sum>i\<le>n. n choose i) = 2^n" by (simp add: choose_row_sum)
      have "n choose (k+1) > 0" using kn_def by auto
        hence ineq_strict1: "(\<Sum>i\<le>k. n choose i) < (\<Sum>i\<le>k+1. n choose i)" by auto
        have "{..k+1} \<subseteq> {..n} \<and> (\<forall>i. n choose i \<ge> 0) \<and> finite {..n}" using kn_def by auto
        hence "(\<Sum>i\<le>k+1. n choose i) \<le> (\<Sum>i\<le>n. n choose i)"
          using sum_mono2[of "{..n}" "{..k+1}" f] by (auto simp add: f_def)
        thus ?thesis using eq_1 ineq_strict1 by presburger
      qed
      define intchoose2X::"int \<Rightarrow> int" where "intchoose2X i = int (2*nat X choose nat i)" for i
      hence ineq_pfrac_2: "\<rho>_frac \<le> sum (\<lambda>i. intchoose2X i ) (set[0..X-1]) *(V w g Y)^(nat (X-1))" 
        using ineq_pfrac_1 by auto
      have eq1: "sum (\<lambda>i. intchoose2X i ) (set[0..X-1]) \<le> (\<Sum>i\<le>nat(X-1). int (2*nat X choose i))"
        using change_sum[of intchoose2X "nat(X-1)"] X_pos intchoose2X_def by auto
      have eq2: "(\<Sum>i\<le>nat(X-1). int (2*nat X choose i)) = int (\<Sum>i\<le>nat(X-1). 2*nat X choose i)"
        by auto
      have "(\<Sum>i\<le>nat(X-1). 2*nat X choose i) < 2^(2*nat X)" using ineq_binom[of "nat(X-1)" "2*nat X"] 
        X_pos by auto
      hence "int (\<Sum>i\<le>nat(X-1). 2*nat X choose i) < 2^(2*nat X)"
        by (metis of_nat_less_iff of_nat_numeral of_nat_power)
      hence eq3: "sum (\<lambda>i. intchoose2X i ) (set[0..X-1]) < 2^(2*nat X)"
        using eq1 eq2 by presburger
      have "(V w g Y)^(nat (X-1)) > 0" using V_pos by auto
      hence "\<rho>_frac < (V w g Y)^(nat (X-1)) * 2^(2*nat X)"
        using eq3 ineq_pfrac_2 mult.commute by (smt (verit, ccfv_SIG) mult_strict_right_mono)
      hence "V w g Y * \<rho>_frac < (V w g Y)^(nat X) * 2^(2*nat X)"
        using mult_strict_left_mono[of \<rho>_frac "(V w g Y)^(nat (X-1)) * 2^(2*nat X)" "V w g Y"]
        V_pos power_Suc[of "V w g Y" "nat (X-1)"] X_pos
        using ab_semigroup_mult_class.mult_ac(1) mult.commute nat_diff_distrib by fastforce
      hence ineq_pfrac_3: "4*w*g*Y*\<rho>_frac < (V w g Y)^nat X * 2^(2*nat X)" using V_def by auto
      have "4*w*g*b*\<rho>_frac \<le> 4*w*g*Y*\<rho>_frac" 
        using \<rho>_frac_pos assms wBeb by (smt (z3) mult_less_cancel_left2 mult_mono)
      hence "4*g*(b*w)*\<rho>_frac \<le> 4*w*g*Y*\<rho>_frac" by (auto simp add: algebra_simps)
      hence ineq_p_frac_4: "4*g*2^(nat (B X))* \<rho>_frac \<le> 4*w*g*Y*\<rho>_frac"
        using sat_4_2d d2d_def[of b w X] by force
      have "nat (B X) = Suc (2*nat X)" using B_def[of X] X_pos by auto
      hence "8*g* \<rho>_frac * 2^(2*nat X) \<le> 4*w*g*Y*\<rho>_frac"
        using power_Suc[of 2 "2*nat X"] ineq_p_frac_4 by auto
      hence "8*g*\<rho>_frac*2^(2*nat X) < (V w g Y)^nat X * 2^(2*nat X)" using ineq_pfrac_3 by presburger
      thus ?thesis by auto
    qed

    have UV_pos: "U l X Y * V w g Y \<ge> 0" using UBe2 V_pos by auto
    have "C l w h g Y X = \<psi> (A l w g Y X) (nat (B X))"
      unfolding C_def using h_def2 by auto
    hence C_def2: "C l w h g Y X = \<psi> (U l X Y * (V w g Y + 1)) (2*nat X +1)"
      unfolding A_def B_def using X_pos by (smt (z3) mult_2 nat_add_distrib nat_numeral 
          one_eq_numeral_iff)
    have "2*X \<le> U l X Y" unfolding U_def L_def using X_pos assms(2) lBeb assms(1) b_def
      by (smt (verit, ccfv_threshold) mult_le_cancel_left1)
    hence "2*int(nat X) \<le> U l X Y \<and> nat X \<ge> 1" using X_pos by auto
    hence "abs (U l X Y * V w g Y * ((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) * 
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1)))
      \<le> 2*X*(V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      using lemma_4_4_cor[of "nat X" "U l X Y" "V w g Y"] assms C_def2 VBe1 by auto
    hence "U l X Y * V w g Y * abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le> 2*X*(V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)"
      using UV_pos abs_mult[of "U l X Y * V w g Y" "((V w g Y)^nat X * C l w h g Y X 
        - (V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))"] by auto
    hence "V w g Y * U l X Y * abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le> 2*X*(V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)"
      by (auto simp add: algebra_simps)
    hence "(2*X)*L l Y*V w g Y*abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le> (2*X)*(V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)"
      unfolding U_def by (auto simp add: algebra_simps)
    hence "L l Y*V w g Y*abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le> (V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)"
      using X_pos by auto
    hence ineq_abs_1: "int \<rho>_int * V w g Y*abs (((V w g Y)^nat X * C l w h g Y X 
      - (V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le> (V w g Y + 1)^(2*nat X) 
      * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      unfolding L_def using l_def2 by auto
    have psi_pos: "\<psi> ((U l X Y)^2*V w g Y) (nat X +1) > 0" 
      using lucas_strict_monotonicity[of "(U l X Y)^2*V w g Y" "nat X"] U2VBe2 by auto
    have \<rho>_int_pos: "int \<rho>_int > 0" using l_def2 lBeb assms b_def by auto
    have \<rho>_Le_2pint: "(V w g Y + 1)^(2*nat X) \<le> int \<rho>_int*2*V w g Y ^nat X"
    proof -
      have "\<rho>_frac \<le> 8*g*\<rho>_frac" using assms \<rho>_frac_pos
        by (metis mult_mono mult_numeral_1 mult_right_mono numeral_One one_le_numeral zero_le_numeral)
      hence maj_\<rho>_frac1: "\<rho>_frac \<le> V w g Y ^nat X" using \<rho>_frac_L_inv8g by auto
      have "int \<rho>_int > 0 \<and> V w g Y ^nat X \<ge> 0" using \<rho>_int_pos V_pos by auto
      hence "\<rho>_frac \<le> int \<rho>_int * V w g Y ^ nat X"
        by (smt (verit, ccfv_threshold) maj_\<rho>_frac1 mult_le_cancel_right1)
      hence "\<rho>_frac \<le> V w g Y ^nat X * int \<rho>_int" by (auto simp add :algebra_simps)
      hence "(V w g Y + 1)^(2*nat X) \<le> 2*V w g Y ^nat X*int \<rho>_int" using decomp_of_p 
        add_mono[of "V w g Y ^nat X*int \<rho>_int" "V w g Y ^nat X*int \<rho>_int" \<rho>_frac 
        "V w g Y ^nat X*int \<rho>_int"] by auto
      thus ?thesis by (auto simp add: algebra_simps)
    qed
    hence "int \<rho>_int * V w g Y*abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le>  int \<rho>_int * 2 * V w g Y ^nat X 
      * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      using ineq_abs_1 psi_pos mult_right_mono[of "(V w g Y + 1)^(2*nat X)" "int \<rho>_int * 2 
        * V w g Y ^nat X" "\<psi> ((U l X Y)^2*V w g Y) (nat X +1)"] by linarith
    hence ineq_abs_2: "V w g Y*abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<le>  2 * V w g Y ^nat X * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      using \<rho>_int_pos by auto
    have VBe32g: "V w g Y \<ge> 32*g"
    proof -
      have "V w g Y = 4*g*w*Y" unfolding V_def by simp
      hence "V w g Y \<ge> 4*g*(b*w)" using assms wBeb b_def by auto
      hence "V w g Y \<ge> 4*g*2^nat (B X)" using sat_4_2d d2d_def[of b w X] by auto
      hence "V w g Y \<ge> 4*g*2^(nat(2*X+1))" unfolding B_def by auto
      hence "V w g Y \<ge> 4*g*2^3" using X_pos power_increasing[of 3 "nat (2*X+1)" 2]
        by (smt (z3) BBe3 B_def g_def zmult_zless_mono2)
      thus ?thesis by auto
    qed
    have "U l X Y * abs (((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1))) \<ge> 0"
      using UBe2 by auto
    hence "32*g * abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> 2*V w g Y ^nat X * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      using ineq_abs_2 VBe32g mult_right_mono[of "32*g" "V w g Y" "abs ((V w g Y)^nat X *
      C l w h g Y X - (V w g Y + 1)^(2*nat X) * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))"] by auto
    hence ineq_abs_3: "16*g*abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y + 1)^(2*nat X) *
      \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> V w g Y ^nat X * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      by auto

    have V_po_X_pos: "(V w g Y)^nat X > 0" using V_pos by auto
    hence "(V w g Y)^nat X * abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))
      = abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1))"
      using abs_mult[of "(V w g Y)^nat X" "C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"]
      by (auto simp add: algebra_simps)
    hence "(V w g Y)^nat X * abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le>
      abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)) + abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) -
      (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" 
      using abs_triangle_ineq[of "(V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)
        *\<psi> ((U l X Y)^2*V w g Y) (nat X +1)" "(V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) 
        (nat X +1) - (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"] by auto
    hence "16*g*(V w g Y)^nat X * abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le>
      16*g*(abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)) + abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) -
      (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)))"
      using mult_left_mono[of "(V w g Y)^nat X * abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y)
        (nat X +1))" "abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)
        *\<psi> ((U l X Y)^2*V w g Y) (nat X +1)) + abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) 
          (nat X +1) - (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" "16*g"] assms 
      by auto
    hence ineq_abs_4: "16*g*(V w g Y)^nat X * abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1)) \<le> 16*g*abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)
      *\<psi> ((U l X Y)^2*V w g Y) (nat X +1)) + 16*g*abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y)
      (nat X +1) - (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" 
      by (auto simp add: algebra_simps)
    have "abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) -
      (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) = abs (((V w g Y +1)^(2*nat X)
      - (V w g Y)^nat X * int \<rho>_int) * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" using l_def2 L_def[of l Y]
      by (auto simp add: algebra_simps)
    hence "abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) - (V w g Y)^nat X 
      * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) = abs ((V w g Y +1)^(2*nat X) - 
      (V w g Y)^nat X * int \<rho>_int) * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      using abs_mult[of "(V w g Y +1)^(2*nat X) - (V w g Y)^nat X * int \<rho>_int" 
        "\<psi> ((U l X Y)^2*V w g Y) (nat X +1)"] psi_pos by auto
    hence "abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) - (V w g Y)^nat X *
      L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> abs \<rho>_frac * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)"
      using decomp_of_p by (smt (verit, del_insts))
    hence "16*g*abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) - (V w g Y)^nat X *
      L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> 16*g*(\<rho>_frac*\<psi> ((U l X Y)^2*V w g Y) (nat X +1))" 
      using assms mult_left_mono[of "abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1)
       - (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" "\<rho>_frac*\<psi> ((U l X Y)^2
       *V w g Y) (nat X +1)" "16*g"] \<rho>_frac_pos by auto
    hence "16*g*abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) - (V w g Y)^nat X *
      L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> 8*g*\<rho>_frac*(2*\<psi> ((U l X Y)^2*V w g Y) (nat X +1))"
      by (auto simp add: algebra_simps)
    hence "16*g*abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) - (V w g Y)^nat X *
      L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> (V w g Y)^nat X * (2* \<psi> ((U l X Y)^2*V w g Y) 
      (nat X +1))"
      using \<rho>_frac_L_inv8g mult_right_mono[of "8*g*\<rho>_frac" "(V w g Y)^nat X"
          "2*\<psi> ((U l X Y)^2*V w g Y) (nat X +1)"] psi_pos by linarith
    hence "16*g*abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y)
      (nat X +1)) + 16*g*abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) -
      (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le> V w g Y ^nat X
      * \<psi> ((U l X Y)^2*V w g Y) (nat X +1) + (V w g Y)^nat X * (2* \<psi> ((U l X Y)^2*V w g Y) (nat X +1))"
      using ineq_abs_3 add_mono[of "16*g*abs ((V w g Y)^nat X * C l w h g Y X - (V w g Y +1)^(2*nat X)
      *\<psi> ((U l X Y)^2*V w g Y) (nat X +1))" "V w g Y ^nat X * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)" 
      "16*g*abs ((V w g Y +1)^(2*nat X)*\<psi> ((U l X Y)^2*V w g Y) (nat X +1) -
      (V w g Y)^nat X * L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" 
      "(V w g Y)^nat X * (2*\<psi> ((U l X Y)^2*V w g Y) (nat X +1))"] by blast
    hence "16*g*(V w g Y)^nat X * abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))
       \<le> V w g Y ^nat X * \<psi> ((U l X Y)^2*V w g Y) (nat X +1) + (V w g Y)^nat X 
       * (2 * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))" using ineq_abs_4 by auto
    hence "(V w g Y)^nat X * (16*g*abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)))
      \<le> V w g Y ^nat X * (3*\<psi> ((U l X Y)^2*V w g Y) (nat X +1))" by (auto simp add: algebra_simps)
    hence "16*g*abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)) \<le>
      3*\<psi> ((U l X Y)^2*V w g Y) (nat X +1)" using V_po_X_pos by auto
    hence "16*g*abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))
      < 4*\<psi> ((U l X Y)^2*V w g Y) (nat X +1)" using psi_pos by auto
    hence "4*g*abs (C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1))
      < \<psi> ((U l X Y)^2*V w g Y) (nat X +1)" by auto
    hence ineq_abs_5: "abs (4*g*(C l w h g Y X - L l Y * \<psi> ((U l X Y)^2*V w g Y) (nat X +1)))
      < \<psi> ((U l X Y)^2*V w g Y) (nat X +1)" using assms by (auto simp add: abs_mult)
    have K_is_psi: "K k l w g Y X = \<psi> ((U l X Y)^2*V w g Y) (nat X +1)" using k_def K_def by auto
    hence "abs (4*g*(C l w h g Y X - L l Y * K k l w g Y X))
      < K k l w g Y X" using ineq_abs_5 by auto
    hence "abs (4*g*C l w h g Y X - 4*g*L l Y * K k l w g Y X) < K k l w g Y X" 
      by (auto simp add: algebra_simps)
    hence "abs (4*g*C l w h g Y X - 4*g*L l Y * K k l w g Y X)*abs (4*g*C l w h g Y X 
      - 4*g*L l Y * K k l w g Y X) < K k l w g Y X*K k l w g Y X" using mult_strict_mono[of 
      "abs (4*g*C l w h g Y X - 4*g*L l Y * K k l w g Y X)" "K k l w g Y X" 
      "abs (4*g*C l w h g Y X - 4*g*L l Y * K k l w g Y X)" "K k l w g Y X"] psi_pos K_is_psi by auto
    hence "abs (4*g*C l w h g Y X - 4*g*L l Y * K k l w g Y X)^2 < K k l w g Y X ^2" 
      by (auto simp add: power2_eq_square)
    hence sat_4_2e: "d2e k l w h g Y X" unfolding d2e_def by auto
  
    show "statement2a b Y X g" unfolding statement2a_def using hBeb kBeb lBeb wBeb sat_4_2a sat_4_2d
sat_4_d2b sat_4_d2c sat_4_2e by force

  qed

end (* of context *)

end
