section \<open> Examples of Coppersmith's Method \<close>

text \<open> In this file, we provide some examples of Coppersmith's method,
  with correctness proofs (when applicable). \<close>

theory Coppersmith_Examples

imports Coppersmith
        Towards_Coppersmith
begin

subsection \<open> Example of lightweight method \<close>

text \<open> Following Example 19.1.6 in Galbraith. This example produces [:444, 1, - 20, - 2:],
  which corresponds to $-2x^3 - 20x^2 + x + 444$, which has 4 as a root.
  Computing $4^3+10*4^2+5000*4-222$ produces 20002, which is 0 mod 10001.
  Note that here, we cannot use our top-level correctness result for the lightweight
  method to prove correctness.
  This is because the conditions of this top-level result are not satisfied;
  however, the method succeeds despite not fulfilling the conditions of
  this result, because the LLL algorithm can be better than the bound in 
  the result.  See Example 19.1.6 in "Mathematics of Public Key Cryptography" by Galbraith 
  for more discussion of this. \<close>
value "towards_coppersmith [:-222, 5000, 10, 1:] 10001 10"

subsection \<open> Examples of Coppersmith's method \<close>

(* When calling coppersmith, we want epsilon < 1/d - log_M(2*X) *)
text \<open> Following Exercise 19.1.12 in Galbraith. \\
  This next example produces 
   $15955575444164700778296$ - $86948462676890416832x$ + $50262448764961319x^2$+ $334700479564525x^3$
   - $611446097378x^4$ - $577363178x^5$ + $1008850x^6$ + $8592x^7,$ 
 which has 267 as a root, which is a root of the original polynomial mod $2^9$. \<close>
value "coppersmith [:227, 46976195, 2^25-2883584, 1:] ((2^20 + 7)*(2^21 + 17)) (2^9) 0.089"

text \<open> We now prove that this example satisfies the conditions of
  our top-level correctness theorem for Coppersmith's method. \<close>
lemma coppersmith_finds_small_roots_example1:
  fixes p f:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  fixes k:: "nat"
  defines "p \<equiv> [:227, 46976195, 2^25-2883584, 1:]"
  defines "d \<equiv> degree p"
  defines "M \<equiv> ((2^20 + 7)*(2^21 + 17))"
  defines "X \<equiv> 2^9"
  defines "f \<equiv> coppersmith p M X 0.089"
  assumes x0_le: "\<bar>x0\<bar> \<le> X"
  assumes zero_mod_M: "poly p x0 mod M = 0"
  shows "poly f x0 = 0"
proof - 
  have d_eq_3: "d = 3"
    unfolding d_def p_def by auto
  have "1 / (3::real) - 89 / 10 ^ 3 = 733/3000"
    by auto
  have all_prop: "\<And> A B :: nat. real A < B \<Longrightarrow> real A powr n < B powr n" if "n > 0" for n 
    by (simp add: powr_less_mono2 that)
  have "real ((2 ^ 20*2 ^ 21)) < real ((2 ^ 20 + 7) * (2 ^ 21 + 17))"
    by simp
  then have lt:  "real ((2 ^ 20*2 ^ 21)) powr (733/3000) < real ((2 ^ 20 + 7) * (2 ^ 21 + 17)) powr (733/3000)"
    using all_prop[of "(733/3000)" "(2 ^ 20*2 ^ 21)" "(2 ^ 20 + 7) * (2 ^ 21 + 17)"] 
    by argo
  have "\<And> b:: nat. (real 2^b) powr c = 2 powr (b*c)" for c::real
    by (smt (verit) Num.of_nat_simps(4) Suc_1 of_nat_1 plus_1_eq_Suc powr_powr powr_realpow)
  then have "(2::real) powr (41 * (733 / 3000)) = (2 ^ 41) powr (733 / 3000)"
      by (metis numeral_powr_numeral_real powr_powr) 
  then have lt1: "(((2::nat) ^ 20*2 ^ 21)) powr (733/3000) = 2 powr (41*733/3000)"
    by simp
  have "41*733/3000 > real 10"
    by simp
  then have "2 powr 10 < real 2 powr (41*733/3000)"
    by (metis less_num_simps(2) numeral_code(1) numeral_less_iff of_nat_numeral powr_less_mono)
  then have "2^10 < real ((2 ^ 20 + 7) * (2 ^ 21 + 17)) powr (1 / (3::real) - 89 / 10 ^ 3)"
    using lt lt1 by auto
  then have root_bound: "real X < root_bound M (degree p) 0.089"
    unfolding M_def X_def root_bound_def using d_eq_3 unfolding d_def
    by simp
  show ?thesis
  using coppersmith_finds_small_roots_pretty[OF _ _ _ _ zero_mod_M root_bound x0_le]
  unfolding p_def M_def f_def X_def by auto
qed

text \<open> In this next example, we are trying to find small roots less than 3 of
  $x^3 + 1000x^2 + 25 + 1$ mod 4059. Running "coppersmith" on this example yields
  [:41858, - 28457, 6100, 376, 150, - 31, - 91, - 28, - 17:], which corresponds to
  $-17x^8 - 28x^7 - 91x^6 - 31x^5 + 150x^4 + 376x^3 + 6100x^2 -28457x+ 41858$, which
  has 2 as a root. Plugging in $2^3 + 1000*2^2 + 25*2 + 1$ indeed yields 4059, which is 0 mod 4059. \<close>
value "form_basis_coppersmith [:1, 25, 1000, 1:] 4059 3 (calculate_h_coppersmith [:1, 25, 1000, 1:]  0.10)"
value "reduce_basis 2 (form_basis_coppersmith [:1, 25, 1000, 1:] 4059 3 (calculate_h_coppersmith [:1, 25, 1000, 1:]  0.10))"
value "coppersmith [:1, 25, 1000, 1:] 4059 3 0.10"

text \<open> We now prove that this example satisifes the conditions of
  our top-level correctness theorem for Coppersmith's method. \<close>
lemma coppersmith_finds_small_roots_example2:
  fixes p f:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  fixes k:: "nat"
  defines "p \<equiv> [:1, 25, 1000, 1:]"
  defines "d \<equiv> degree p"
  defines "M \<equiv> 4059"
  defines "X \<equiv> 3"
  defines "f \<equiv> coppersmith p M X 0.10"
  assumes x0_le: "\<bar>x0\<bar> \<le> X"
  assumes zero_mod_M: "poly p x0 mod M = 0"
  shows "poly f x0 = 0"
proof - 
  have d_eq_3: "d = 3"
    unfolding d_def p_def
    by simp
 have "\<And> a b:: nat. (real 4059 powr c) ^ b = 4059 powr (b*c)" for c::real
   using Suc_1 plus_1_eq_Suc powr_powr powr_realpow
   by (smt (verit) Groups.mult_ac(2) Num.of_nat_simps(2) numeral_Bit0 numeral_Bit1 numeral_One of_nat_numeral powr_gt_zero)   
  then have simplify_power:"(real 4059 powr (7/30))^30 = 4059 powr 7"
    by auto
  have gt: "(4059::real)/(6^4) > 3"
    by auto
  have "(6::real)^28 = 6^(4*7)"
    by auto
  then have h1: "(6::real)^28 = (6^4)^7"
    by (metis power_mult)
  have all_div: "\<And>a b c::real. b > 0 \<Longrightarrow> a < c/b \<Longrightarrow> a*b < c"
    by (simp add: pos_less_divide_eq)
  have h2: "real 6^30 = 6^28*6^2"
    by simp
  have "((4059)^7::real)/((6^4)^7) = (4059/6^4)^7"
    by (metis power_divide)
  then have "((4059)^7::real)/((6^4)^7) > 3^7"
    using gt by simp
  then have "real 6^2 < (4059)^7/((6^4)^7)"
    by simp
  then have "real 6^2*((6^4)^7) < (4059)^7"
    using all_div[of "(6^4)^7" "6^2" "(4059)^7"]
    by simp
  then have "real 6^30 < 4059 ^ 7"
    using h1 h2 by simp
  then have "real 6^30 < (real 4059 powr (7/30))^30"
    using simplify_power by fastforce
  then have "real 6 < real 4059 powr (7/30)"
    by (smt (verit) of_nat_0_less_iff powr_gt_zero powr_less_mono2 powr_realpow semiring_norm(118))
  then have root_bound: "real X < root_bound M (degree p) 0.10"
    unfolding M_def X_def root_bound_def using d_eq_3 unfolding d_def
    by auto
  show ?thesis
  using coppersmith_finds_small_roots_pretty[OF _ _ _ _ zero_mod_M root_bound x0_le]
  unfolding p_def M_def f_def X_def by auto
qed


end