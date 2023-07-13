theory More_Bit_Operations_Nat
imports 
  "HOL.Bit_Operations"
begin

text \<open>
In the process of translating Cypto Standards to HOL, I needed some facts about bit operations
on natural numbers that were not (at least at that time) available in HOL.  
\<close>


notation
         not  (\<open>NOT\<close>)
    and "and" (infixr \<open>AND\<close> 64)
    and   or  (infixr \<open>OR\<close>  59)
    and  xor  (infixr \<open>XOR\<close> 59)

declare [[coercion_enabled]]
declare [[coercion int]]

section \<open>Bit Operations on Nats or Ints\<close>

text \<open>The following was proved for integers.  Here we prove them for naturals. \<close>
lemma nat_OR_upper:
  fixes    b s :: nat
  assumes "b < 2^n" "s < 2^n" 
  shows   "b OR s < 2^n"
  using assms OR_upper or_nat_def by force

lemma nat_AND_upper:
  fixes  x y :: nat
  shows "x AND y \<le> x"
  by (simp add: and_nat_def nat_le_iff) 

lemma nat_AND_upper2:
  fixes  x :: nat
    and  y :: int
  shows "x AND y \<le> x"
  using AND_upper1 by force 

lemma nat_NAND_upper:
  fixes  x y :: nat
  shows "x AND (NOT y) \<le> x"
  using nat_AND_upper by simp 

lemma nat_XOR_upper:
  fixes    x y :: nat
  assumes "x < 2 ^ n" "y < 2 ^ n"
  shows   "x XOR y < 2 ^ n"
  using assms XOR_upper xor_nat_def by simp

lemma XOR_power_mod_int: "(a XOR b :: int) mod 2^n = (a mod 2^n) XOR (b mod 2^n)"
  by (metis take_bit_int_def take_bit_xor)

lemma XOR_power_mod_nat:
  fixes   a b :: nat
  shows "(a XOR b) mod 2^n = a mod 2^n XOR b mod 2^n"
  by (metis take_bit_nat_def take_bit_xor)

text \<open>The following was true for words, but I needed it for naturals.  So first I showed it for
integers and second I proved it for naturals. \<close>
lemma shiftr_over_or_dist_int:
  fixes  a b :: int
  shows "((a OR b) div 2^n) = ((a div 2^n) OR (b div 2^n))"
  by (metis drop_bit_int_def drop_bit_or)

lemma shiftr_over_or_dist_nat:
  fixes  a b :: nat
  shows "((a OR b) div 2^n) = ((a div 2^n) OR (b div 2^n))"
  by (metis drop_bit_nat_def drop_bit_or)

lemma mod_over_or_dist_int:
  fixes  a b :: int
  shows "((a OR b) mod 2^n) = ((a mod 2^n) OR (b mod 2^n))"
  by (metis take_bit_int_def take_bit_or)

lemma mod_over_or_dist_nat:
  fixes  a b :: nat
  shows "((a OR b) mod 2^n) = ((a mod 2^n) OR (b mod 2^n))"
  by (metis take_bit_nat_def take_bit_or)

text \<open>The idea of "hilo" or "high/low" is inspired values that fit inside two machine words.
We generalize these lemmas for any size n of the machine, say n=32 or n=64.\<close>
lemma OR_shiftn_of_nat_hilo: 
  fixes    b c s t:: nat
  assumes "b < 2^n" "s < 2^n" 
  shows   "((2^n * c + b) OR (2^n*t + s)) div 2^n = (c OR t)"
  by (simp add: assms shiftr_over_or_dist_nat)

lemma OR_power_mod_nat_hilo:
  fixes    b c s t:: nat
  assumes "b < 2^n" "s < 2^n" 
  shows   "((2^n* c + b) OR (2^n*t + s)) mod 2^n = b OR s"
  by (simp add: assms mod_over_or_dist_nat)

lemma OR_sum_nat_hilo:
  fixes    b c s t:: nat
  assumes "b < 2^n" "s < 2^n"
  shows   "2^n*(c OR t) + (b OR s) = (2^n* c + b) OR (2^n*t + s)"
  by (metis OR_power_mod_nat_hilo OR_shiftn_of_nat_hilo assms mult_div_mod_eq)

lemma OR_sum_nat_hilo_2:
  fixes    c s n:: nat
  assumes "s < 2^n"
  shows   "2^n* c + s = 2^n* c OR s"
proof - 
  have "(0::nat) < 2^n"  by presburger
  then have "2^n*(c OR 0) + (0 OR s) = (2^n* c + 0) OR (2^n*0 + s)" 
    using assms OR_sum_nat_hilo by blast
  then have "2^n*(c OR 0) + (0 OR s) = 2^n* c OR s"
    using add_0_right mult_0_right add_0_left by force
  then show "2^n* c + s = 2^n* c OR s"  using or_nat_def by fastforce
qed

lemma AND_zero_OR_eq_XOR:
  fixes   a b :: nat
  assumes "a AND b = 0"
  shows   "a OR b = a XOR b"
  by (metis (mono_tags, lifting) and_eq_not_not_or assms bit.de_Morgan_conj bit.xor_def2 
      nat_int_comparison(1) of_nat_0 of_nat_and_eq of_nat_or_eq of_nat_xor_eq or.right_neutral 
      or_eq_not_not_and)

lemma hilo_AND_zero_h:
  fixes    c s n i :: nat
  assumes "s < 2^n"
  shows   "bit (2^n* c AND s) i = False"
proof (cases "i < n") 
  case A0: True
  have A1: "0 < n - i"              by (simp add: A0) 
  have A2: "2^n* c div 2^i = 2^(n-i)* c"
    by (metis A0 dvd_div_mult dvd_triv_left le_add_diff_inverse less_or_eq_imp_le power_add 
             power_diff zero_neq_numeral) 
  have A3: "even (2^(n-i)* c)"      using A1 by force 
  have A4: "bit (2^n* c) i = False" using A2 A3 bit_nat_def by presburger 
  show ?thesis                      by (simp add: A4 bit_and_iff) 
next
  case False
  then have B0: "n \<le> i"       by (meson not_le)
  have B1: "s div 2^i = 0"    
    by (smt (verit, del_insts) assms B0 Euclidean_Rings.div_eq_0_iff div_mult2_eq le_iff_add 
        power_add zero_less_numeral zero_less_power) 
  have B2: "even (s div 2^i)" by (simp add: B1)
  have B3: "bit s i = False"  by (simp add: B1 bit_nat_def) 
  show ?thesis                by (simp add: B3 bit_and_iff)
qed

lemma hilo_AND_zero:
  fixes    c s n:: nat
  assumes "s < 2^n"
  shows   "(2^n* c) AND s = 0"
proof -
  have "\<forall>j. bit (2^n* c AND s) j = False"  by (simp add: assms hilo_AND_zero_h) 
  then show ?thesis                        by (simp add: bit_eq_iff) 
qed

lemma XOR_sum_nat_hilo_2:
  fixes    c s n:: nat
  assumes "s < 2^n"
  shows   "2^n* c + s = 2^n* c XOR s"
  using assms AND_zero_OR_eq_XOR hilo_AND_zero OR_sum_nat_hilo_2 by presburger

lemma int_OR:
  fixes  a b :: nat
  shows "int (a OR b) = int(a) OR int(b)"
  by (simp add: or_nat_def)

lemma OR_sum_int_hilo_2:
  fixes    c s :: int
  and      n   :: nat
  assumes "s < 2^n" "0 \<le> c" "0 \<le> s"
  shows   "2^n* c + s = 2^n* c OR s"
proof - 
  let ?C = "nat c"
  let ?S = "nat s"
  have 1: "?S < 2^n"                                    using assms(1) by simp
  have 2: "2^n*?C + ?S = 2^n*?C OR ?S"                  using 1 OR_sum_nat_hilo_2 by blast
  have 3: "int ?C = c"                                  using assms(2) by presburger
  have 4: "int ?S = s"                                  using assms(3) by presburger
  have 5: "int (2^n*?C + ?S) = 2^n* c + s"              using 3 4 by auto
  have 6: "int (2^n*?C OR ?S) = int(2^n*?C) OR int(?S)" using int_OR by blast
  have 7: "int (2^n*?C OR ?S) = 2^n* c OR s"            using 3 4 6 by force
  then show ?thesis                                     using 2 5 7 by argo
qed

lemma sum_int_hilo:
  fixes c s :: int
  and   n m :: nat
  assumes "s < 2^n" "0 \<le> c" "0 \<le> s" "c < 2^m"
  shows   "(2^n)* c + s < 2^(n+m)"
proof - 
  have 1: "2^n* c + s = 2^n* c OR s"  using assms(1,2,3) OR_sum_int_hilo_2 by blast
  have 2: "2^n* c < 2^n*2^m"          using assms(4) by simp
  have 3: "1 < (2::int)"              by presburger
  have 4: "(2::int)^n*2^m = 2^(n+m)"  by (simp add: 3 power_add) 
  have 5: "n \<le> (n+m)"                 by simp
  have 6: "s < 2^(n+m)"               by (smt (verit, ccfv_SIG) assms(1) 5 power_increasing_iff)
  have 7: "2^n* c < 2^(n+m)"          using 2 4 by presburger
  have 8: "2^n* c OR s < 2^(n+m)"     using 6 7 OR_upper assms(2) by auto
  show ?thesis                        using 1 8 by presburger
qed

end