theory Bridge_Theorem_Rev
  imports "../Lucas_Sequences/DFI_square_3" 
          Bridge_Theorem_Imp
          "HOL-Computational_Algebra.Primes"
begin

lemma div_pow':
  fixes a::real and n::nat and p::nat
  assumes "n\<ge>p" and "a\<noteq>0"
  shows "a^n / a^p = a^(n-p)"
proof -
  have "a^p * a^(n-p) = a^n" using assms power_add[of a "p" "n-p"] by fastforce
  hence "a^p * a^(n-p) / a^p = a^n / a^p" using assms divide_cancel_right by fastforce
  thus ?thesis using assms by fastforce
qed

lemma inv_decr:
  fixes a::real and b::real
  assumes "a \<ge> b" and "b > 0"
  shows "1/a \<le> 1/b"
  by (simp add: assms(1) assms(2) frac_le)

lemma div_pow:
  fixes a::real and n::nat and m::nat
  assumes "m<n" and "a\<noteq>0"
  shows "a^n/a^m = a*a^(n-m-1)"
proof -
  have "Suc (n-m-1) = n-m \<and> (n-m)+m = n" using assms by (auto simp add: algebra_simps)
  hence "a*a^(n-m-1)*a^m = a^n" using power_Suc[of a "n-m-1"] power_add[of a "n-m" m] by auto
  thus ?thesis by (metis assms(2) nonzero_mult_div_cancel_right power_eq_0_iff)
qed


lemma power_majoration:
  fixes a::real and n::nat
  assumes "0 < a" and "a \<le> 1"
  shows "(1+a)^n \<le> 1 + (2^n-1)*a"
proof (induction n)
  case 0
then show ?case using assms by auto
next
  case (Suc n)
  note t = this
  have "(1+a)^(Suc n) = (1+a)*(1+a)^n" using power_Suc by auto
  hence "(1+a)^(Suc n) \<le> (1+a)*(1+(2^n-1)*a)" using t assms by auto
  hence "(1+a)^(Suc n) \<le> 1+a + (1+a)*((2^n-1)*a)" by (auto simp add: algebra_simps)
  hence "(1+a)^(Suc n) \<le> 1 + a + 2*(2^n-1)*a" using assms mult_right_mono[of "1+a" 2 "(2^n-1)*a"]
    by (smt (verit, ccfv_SIG) one_le_power ring_class.ring_distribs(2) t)
  hence "(1+a)^(Suc n) \<le> 1 + (2*2^n-1)*a" by (auto simp add: algebra_simps)
  then show ?case using power_Suc[of 2 n] by auto
qed

lemma div_reg:
  fixes a::int and b::int and c::int and d::int
  assumes "a\<le>b" and "c\<ge>d" and "d>0" and "a\<ge>0"
  shows "a/c \<le> b/d"
proof -
  have "a * d \<le> b * c" using assms mult_mono by fastforce
  hence "real_of_int a * real_of_int d \<le> real_of_int b * real_of_int c"
    by (metis of_int_le_iff of_int_mult)
  thus ?thesis using assms
    by (meson frac_le of_int_0_le_iff of_int_0_less_iff of_int_le_iff order.trans)
qed

lemma lucas_modN_int:
  fixes \<alpha>::int and m::int
  shows "\<psi>_int \<alpha> m mod (\<alpha> - 2) = m mod (\<alpha> - 2)"
proof -
  have "\<psi>_int \<alpha> m mod (\<alpha> - 2) = (-1)^(if m \<ge> 0 then 0 else 1) * \<psi> \<alpha> (nat (abs m)) mod (\<alpha> - 2)"
    unfolding \<psi>_int_def by simp
  hence "\<psi>_int \<alpha> m mod (\<alpha> - 2) = (-1)^(if m \<ge> 0 then 0 else 1) * int (nat (abs m)) mod (\<alpha> - 2)"
    using lucas_congruence2[of \<alpha> "nat (abs m)"] mod_mult_cong[of "(-1)^(if m \<ge> 0 then 0 else 1)" "\<alpha>-2"
"(-1)^(if m \<ge> 0 then 0 else 1)" "\<psi> \<alpha> (nat (abs m))" "int (nat (abs m))"] by presburger
  then show ?thesis by auto
qed

subsection \<open>Proof of implication \<open>(2)\<Longrightarrow>(1)\<close>\<close>

lemma (in bridge_variables) theorem_II_2_1:
  assumes b_def:"(b::int)\<ge>0" and Y_def:"(Y::int)\<ge>b\<and>Y\<ge>2^8" and X_def:"(X::int)\<ge>3*b"
          and g_def:"(g::int)\<ge>1"
        shows "(statement2 b Y X g)\<Longrightarrow>(statement1 b Y X)"
proof -
  assume state2: "statement2 b Y X g"
  then obtain h k l w x y where state2_def: "l*x \<noteq> 0 \<and> d2a l w h x y g Y X \<and> d2b k l w x g Y X \<and>
   d2c l w h b g Y X \<and> d2f k l w h g Y X" unfolding statement2_def by auto
  have sat_a: "d2a l w h x y g Y X" using state2_def by auto
  have sat_b: "d2b k l w x g Y X" using state2_def by auto
  have sat_c: "d2c l w h b g Y X" using state2_def by auto
  have sat_f: "d2f k l w h g Y X" using state2_def by auto
  have lx_nonzero: "l \<noteq> 0 \<and> x \<noteq> 0" using state2_def by auto

  have W_nonzero: "W w b \<noteq> 0"
  proof -
    have "W w b = 0 \<Longrightarrow> False"
    proof -
      assume hyp: "W w b = 0"
      hence "(2*A l w g Y X-5) dvd 2"
        using sat_c unfolding d2c_def S_def T_def by auto
      hence "abs (2*A l w g Y X - 5) \<le> 2"
        using dvd_imp_le_int by presburger
      hence "2*A l w g Y X \<le> 7 \<and> 2*A l w g Y X \<ge> 3" by auto
      hence A_is_2_or_3: "A l w g Y X \<le> 3 \<and> A l w g Y X \<ge> 2" by auto
      have "abs (A l w g Y X) = abs (U l X Y) * abs (V w g Y + 1)"
        unfolding A_def U_def using abs_mult by auto
      hence eq: "abs (A l w g Y X) = 2*X*Y*abs l * abs (V w g Y +1)"
        unfolding U_def L_def using abs_mult[of "2*X" "l*Y"] abs_mult[of 2 X] abs_mult[of l Y] assms
        by auto
      hence X_nonzero: "X \<noteq> 0" using A_is_2_or_3 by auto
      hence several_ineq: "X \<ge> 1 \<and> Y \<ge> 256 \<and> abs l \<ge> 1 \<and> abs (V w g Y +1) \<ge> 0"
        using assms lx_nonzero by auto
      hence "2*X*Y \<ge> 2*256 \<and> abs l \<ge> 1 \<and> abs (V w g Y +1) \<ge> 0"
        using mult_mono[of 1 X 256 Y] mult_left_mono[of 256 "X*Y" 2] by force
      hence "(2*X*Y)*abs l*abs (V w g Y +1) \<ge> (2*256)*abs (V w g Y +1)"
        using mult_mono[of "2*256" "2*X*Y" 1 "abs l"]
          mult_right_mono[of "2*256" "2*X*Y*abs l" "abs (V w g Y +1)"] by linarith
      hence ineq: "2*X*Y*abs l * abs (V w g Y +1) \<ge> 2*256*abs (V w g Y +1)"
        by (auto simp add: mult_mono)
      hence "abs (A l w g Y X) \<ge> 2*256*abs (V w g Y +1)" using ineq eq by presburger
      hence "3 \<ge> 2*256*abs (V w g Y +1) \<and> abs (V w g Y +1) \<ge> 0" using A_is_2_or_3 by auto
      hence "abs (V w g Y +1) = 0"
        by (smt (verit, best) comm_semiring_class.distrib distrib_left distrib_right mult_cancel_left2
            mult_le_0_iff mult_mono ring_class.ring_distribs(1) ring_class.ring_distribs(2))
      hence "V w g Y +1 = 0" by auto
      hence "A l w g Y X = 0" unfolding A_def by auto
      then show "False" using A_is_2_or_3 by auto
    qed
    then show ?thesis by auto
  qed

  hence bBe1: "b \<ge> 1" using assms W_nonzero W_def[of w b] by auto
  hence XBe3: "X \<ge> 3" using X_def by auto
  have absL_Be1: "abs (L l Y) \<ge> 1" unfolding L_def using lx_nonzero assms
    by (smt (z3) bBe1 no_zero_divisors)
  have V_mult_4: "4 dvd V w g Y" unfolding V_def by auto
  hence "V w g Y +1 \<noteq> 0" by presburger
  hence "abs (V w g Y +1) \<ge> 1" by auto
  hence "abs (A l w g Y X) \<ge> abs (U l X Y)"
    unfolding A_def using abs_mult[of "U l X Y" "V w g Y +1"]
      mult_left_mono[of 1 "abs (V w g Y +1)" "abs (U l X Y)"] by auto
  hence "abs (A l w g Y X) \<ge> 2 *X * (abs l * Y) "
    unfolding U_def L_def using abs_mult[of "2*X" "l*Y"] abs_mult[of 2 X] abs_mult[of l Y] XBe3 assms(2)
    by auto
  hence "abs (A l w g Y X) \<ge> 2*X*Y*abs l \<and> abs l \<ge> 1 \<and> 2*X*Y \<ge> 0"
    using lx_nonzero XBe3 assms(2) mult_mono[of 3 X 256 Y]
    by (smt (z3) b_def mult.assoc mult.commute mult_nonneg_nonneg)
  hence "abs (A l w g Y X) \<ge> 2*X*Y" using mult_left_mono[of 1 "abs l" "2*X*Y"] by auto
  hence "abs (A l w g Y X) \<ge> 2*X*Y \<and> Y \<ge> 4 \<and> 2*X \<ge> 0" using mult_mono[of 0 2 3 X] XBe3 assms(2) by simp
  hence "abs (A l w g Y X) \<ge> 8*X" using mult_left_mono[of 4 Y "2*X"] by auto
  hence "abs (A l w g Y X) \<ge> 4*X + 4*X" by auto
  hence "abs (A l w g Y X) > 4*X + 4" using mult_strict_left_mono[of 1 X 4] XBe3 by auto
  hence abs_A_B_2Bp2: "abs (A l w g Y X) > 2*B X + 2" unfolding B_def by auto
  hence abs_A_Be16: "abs (A l w g Y X) \<ge> 16"
    unfolding B_def using XBe3 assms(2) mult_mono[of 2 X 4 Y] by auto
  have abs_Am2_B_2B: "abs (A l w g Y X) - 2 > 2*B X" using abs_A_B_2Bp2 by auto
  have B_B1: "abs (B X) > 1" unfolding B_def using XBe3 by auto
  have Am2_dvd_CmB: "(A l w g Y X-2) dvd (C l w h g Y X-B X)" unfolding C_def by auto
  have D_eq_D: "D_f (A l w g Y X) (C l w h g Y X) = D l w h g Y X" unfolding D_f_def D_def by auto
  hence E_eq_E: "E_ACx (A l w g Y X) (C l w h g Y X) x = E l w h x g Y X"
    unfolding E_ACx_def E_f_def E_def by auto
  hence F_eq_F: "F_ACx (A l w g Y X) (C l w h g Y X) x = F l w h x g Y X"
    unfolding F_ACx_def F_f_def F_def by auto
  hence G_eq_G: "G_ACx (A l w g Y X) (C l w h g Y X) x = G l w h x g Y X"
    unfolding G_ACx_def G_f_def G_def using D_eq_D E_eq_E by auto
  hence H_eq_H: "H_ABCxy (A l w g Y X) (B X) (C l w h g Y X) x y = H l w h x y g Y X"
    unfolding H_ABCxy_def H_f_def H_def using F_eq_F by auto
  hence I_eq_I: "I_ABCxy (A l w g Y X) (B X) (C l w h g Y X) x y = I l w h x y g Y X"
    unfolding I_ABCxy_def I_f_def I_def using G_eq_G by auto
  hence DFI_square: "is_square (D_f (A l w g Y X) (C l w h g Y X) * F_ACx (A l w g Y X) (C l w h g Y X) x
    * I_ABCxy (A l w g Y X) (B X) (C l w h g Y X) x y)"
    using sat_a is_square_def D_eq_D F_eq_F unfolding d2a_def by simp
  hence C_is_\<psi>BA: "C l w h g Y X = \<psi>_int (A l w g Y X) (B X)"
    using sun_theorem[of "B X" "A l w g Y X" "C l w h g Y X" x y] B_B1 abs_Am2_B_2B 
      Am2_dvd_CmB lx_nonzero by (smt (z3) B_def XBe3)

  have w_nonzero: "w \<noteq> 0" using W_nonzero W_def[of w b] by auto
  have B_Be7: "B X \<ge> 7" unfolding B_def using XBe3 by auto
  hence "nat (B X) \<ge> Suc (Suc (Suc 0))" by auto
  then obtain Bm3 where B_3Suc: "Suc (Suc (Suc Bm3)) = nat (B X)"
    by (metis Suc_leD Suc_n_not_le_n rec_forte_init012.cases)
  hence SucSucBm3: "Bm3 + 2 = nat (B X) - 1" by auto
  have "abs (V w g Y) = 4* abs w * g * Y" unfolding V_def
    using abs_mult[of "4*w*g" Y] abs_mult[of "4*w" g] abs_mult[of 4 w] assms(2) assms(4) by auto
  hence "abs (V w g Y) = 4 * abs w * g*Y \<and> abs w \<ge> 1 \<and> g \<ge> 1 \<and> Y \<ge> 2"
    using assms(4) assms(2) w_nonzero by auto
  hence absV_Be8: "abs (V w g Y) \<ge> 8" using mult_left_mono[of 2 Y "4*abs w *g"]
    by (smt (z3) dvd_imp_le_int dvd_triv_left mult_le_0_iff)
  have "abs (U l X Y) = 2*X*abs l*Y \<and> X \<ge> 1 \<and> Y \<ge> 1" and abs_lBe1: "abs l \<ge> 1"
    unfolding U_def L_def using abs_mult[of "2*X" "l*Y"] abs_mult[of 2 X] abs_mult[of l Y]
    XBe3 assms(2) lx_nonzero by auto
  have "abs (U l X Y) = 2*X*abs l*Y \<and> X \<ge> 1 \<and> Y \<ge> 1 \<and> abs l \<ge> 1"
    unfolding U_def L_def using abs_mult[of "2*X" "l*Y"] abs_mult[of 2 X] abs_mult[of l Y] XBe3
    assms(2) lx_nonzero by auto
  hence absUBe2: "abs (U l X Y) \<ge> 2"
    using mult_mono[of 2 "2*X*abs l" 1 Y] mult_mono[of 2 "2*X" 1 "abs l"] mult_left_mono[of 1 X 2]
    by auto
  hence other_ineq_U2: "abs (U l X Y^2) \<ge> 2"
    using power2_eq_square[of "U l X Y"] mult_mono[of 1 "abs (U l X Y)" 2 "abs (U l X Y)"] by auto
  have "abs (V w g Y +1) \<le> abs (V w g Y) +1" by auto
  hence "abs (V w g Y +1) \<le> 2*abs (V w g Y)-1" using absV_Be8 by auto
  hence "abs (V w g Y +1) \<le> abs (U l X Y^2)*abs (V w g Y)-1"
    using other_ineq_U2 mult_right_mono[of 2 "abs (U l X Y^2)" "abs (V w g Y)"] by auto
  hence ineq_Vp1: "abs (V w g Y +1) \<le> abs (U l X Y^2*V w g Y) - 1" using abs_mult by auto
  have "abs (C l w h g Y X) = \<psi> (abs (A l w g Y X)) (nat (abs (B X)))"
    using eq_\<psi>_int[of "A l w g Y X" "B X"] C_is_\<psi>BA abs_A_Be16 by force
  hence "abs (C l w h g Y X) = \<psi> (abs (A l w g Y X)) (nat (B X))" using B_def[of X] XBe3 by auto
  hence "abs (C l w h g Y X) \<le> (abs (A l w g Y X))^(nat (B X)-1)"
    using lucas_exp_growth_lt[of "abs (A l w g Y X)" Bm3] B_3Suc SucSucBm3 abs_A_Be16 by fastforce
  hence "abs (C l w h g Y X) \<le> (abs (U l X Y) * abs( (V w g Y +1)))^(2*nat X)"
    unfolding B_def A_def using XBe3 abs_mult[of "U l X Y" "V w g Y +1"]
    by (smt (z3) mult_2 nat_1 nat_add_distrib nat_diff_distrib numeral_1_eq_Suc_0 numerals(1))
  hence "abs (C l w h g Y X) \<le> (abs (U l X Y))^(2*nat X)*(abs (V w g Y +1))^(2*nat X)"
    using power_mult_distrib[of "abs (U l X Y)" "abs (V w g Y +1)" "2*nat X"] by auto
  hence maj_C1:"abs (C l w h g Y X) \<le> (abs (U l X Y))^(2*nat X)*(abs (U l X Y^2*V w g Y) - 1)^(2*nat X)"
    using ineq_Vp1
    by (smt (verit, ccfv_SIG) int_distrib(1) power_less_imp_less_base zero_le_even_power' zmult_zless_mono2)

  have "is_square ((U l X Y^4*V w g Y^2 - 4)*(K k l w g Y X)^2+4)"
    using sat_b is_square_def unfolding d2b_def by auto
  hence "is_square (((U l X Y^2*U l X Y^2)*(V w g Y*V w g Y) - 4)*(K k l w g Y X)^2+4)"
    using power_add[of "U l X Y" 2 2] power2_eq_square[of "V w g Y"] by auto
  hence "is_square (((U l X Y^2*V w g Y)^2-4)*(K k l w g Y X)^2+4)"
    using power2_eq_square[of "U l X Y^2*V w g Y"] by (auto simp add: algebra_simps)
  then obtain R where R_def: "K k l w g Y X = \<psi>_int (U l X Y^2*V w g Y) R"
    using lucas_pell_corollary_int[of "U l X Y^2*V w g Y" "K k l w g Y X"] is_square_def by auto
  have abs_U2V_B2: "abs (U l X Y^2*V w g Y) > 2"
    using abs_mult[of "U l X Y^2" "V w g Y"] other_ineq_U2 absV_Be8
    mult_strict_mono[of 1 "abs (U l X Y^2)" 2 "abs (V w g Y)"] by force
  have "(X+1) mod (U l X Y^2*V w g Y - 2) = K k l w g Y X mod (U l X Y^2*V w g Y - 2)"
    unfolding K_def by auto
  hence "(X+1) mod (U l X Y^2*V w g Y - 2) = \<psi>_int (U l X Y^2*V w g Y) R mod (U l X Y^2*V w g Y - 2)"
    using R_def by auto
  hence "(X+1) mod (U l X Y^2*V w g Y - 2) = R mod (U l X Y^2*V w g Y - 2)"
    using lucas_modN_int[of "U l X Y^2*V w g Y" R] by auto
  hence "(X+1-R) mod (U l X Y^2*V w g Y-2) = 0 mod (U l X Y^2*V w g Y-2)"
    using mod_diff_cong[of "X+1" "U l X Y^2*V w g Y-2" R R R] by auto
  hence "U l X Y^2*V w g Y-2 dvd (R-(X+1))" by algebra
  then obtain r where "R -(X+1) =r*(U l X Y^2*V w g Y-2)" by force
  hence r_def: "R = X+1+r*(U l X Y^2*V w g Y-2)" by auto

  have r_0: "r \<noteq> 0 \<Longrightarrow> False"
  proof -
    assume hyp: "r \<noteq> 0"
    hence "abs R \<ge> abs (r*(U l X Y^2*V w g Y -2)) - abs (X+1)" using r_def by auto
    hence "abs R \<ge> abs r * abs (U l X Y^2*V w g Y - 2) - X - 1" using abs_mult XBe3 by auto
    hence "abs R \<ge> abs (U l X Y^2*V w g Y - 2) - X - 1"
      using hyp mult_right_mono[of 1 "abs r" "abs (U l X Y^2*V w g Y - 2)"] by force
    hence "abs R \<ge> abs (U l X Y^2*V w g Y) - X - 3" by auto
    hence "abs R \<ge> abs (U l X Y*U l X Y*V w g Y) - X - 3"
      using power2_eq_square[of "U l X Y"] by auto
    hence "abs R \<ge> abs (U l X Y)*(abs (U l X Y)*abs (V w g Y)) - X - 3" by (auto simp add: abs_mult)
    hence "abs R \<ge> abs (U l X Y) - X - 3"
      using absV_Be8 absUBe2 mult_mono[of 1 "abs (U l X Y)" 1 "abs (V w g Y)"]
      mult_left_mono[of 1 "abs (U l X Y) * abs (V w g Y)" "abs (U l X Y)"] by auto
    hence "abs R \<ge> 2*X* (abs l *Y) - X - 3 \<and> Y \<ge> 4 \<and> abs l \<ge> 1 \<and> 2*X \<ge> 0"
      unfolding U_def L_def using assms(2) lx_nonzero XBe3 by auto
    hence "abs R \<ge> 8*X - X - 3"
      using mult_mono[of 1 "abs l" 4 Y] mult_left_mono[of 4 "abs l * Y" "2*X"] by linarith
    hence "abs R > 4*X + 4 - X - 3" using XBe3 by auto
    hence ineq_absR: "abs R > 3*X +1" by auto
    hence ineq_absRm1: "abs R - 1 > 3*X" by auto
       have aRBe2: "nat (abs R) \<ge> 2" using XBe3 ineq_absR by simp
       have "abs (K k l w g Y X) = \<psi> (abs (U l X Y^2*V w g Y)) (nat (abs R))"
         using R_def eq_\<psi>_int abs_U2V_B2 by force
    hence 0: "abs (K k l w g Y X) \<ge> (abs (U l X Y^2*V w g Y) - 1) ^ (nat (abs R) - 1)"
      using abs_U2V_B2 aRBe2 lucas_exp_growth_gt[of "abs (U l X Y^2*V w g Y)" "nat (abs R) - 2"] Suc_eq_plus1
      by (smt (verit, ccfv_SIG) One_nat_def add_2_eq_Suc' add_diff_cancel_left' le_add_diff_inverse2 plus_1_eq_Suc)
    have "nat (abs R) - 1 \<ge> 3 * nat X" using XBe3 ineq_absRm1 by auto
    hence min_K: "abs (K k l w g Y X) \<ge> (abs (U l X Y^2*V w g Y) - 1) ^ (3 * nat X)"
      using 0 abs_U2V_B2 power_increasing[of "3 * nat X" "nat (abs R) - 1" "abs (U l X Y^2*V w g Y) - 1"]
      by linarith

    have "abs (V w g Y) \<ge> 8" using absV_Be8 by blast
    hence "abs ((U l X Y)^2 * V w g Y) \<ge> 8 * (U l X Y)^2"
      by (metis abs_mult_pos mult.commute mult_right_mono power2_eq_square zero_le_square)
    hence "abs ((U l X Y)^2 * V w g Y) - 1 \<ge> 2 * (abs (U l X Y))^2"
      using abs_U2V_B2 by auto
    hence "2* (abs (U l X Y))^2 / (abs (U l X Y^2*V w g Y) - 1) \<le> 1"
      using abs_U2V_B2 by (smt (verit) divide_le_eq_1_pos of_int_le_1_iff of_int_le_iff)
    hence min_U2V: "(abs (U l X Y))^2 / (abs (U l X Y^2*V w g Y) - 1) \<le> 1/2" by linarith
    have B0: "abs (C l w h g Y X) \<ge> 0 \<and> (abs (U l X Y^2*V w g Y) - 1)^(3*nat X) > 0"
      using abs_U2V_B2 by auto
    hence 1: "abs (C l w h g Y X) / abs (K k l w g Y X) \<le> (abs (U l X Y))^(2*nat X) *
      (abs (U l X Y^2*V w g Y) - 1)^(2*nat X) / (abs (U l X Y^2*V w g Y) - 1)^(3*nat X)"
      using min_K maj_C1 div_reg by presburger

    have "(abs (U l X Y))^(2*nat X) * (abs (U l X Y^2*V w g Y) - 1)^(2*nat X) * (abs (U l X Y^2*V w g Y) - 1)^(nat X)
      = (abs (U l X Y))^(2*nat X) * (abs (U l X Y^2*V w g Y) - 1)^(3*nat X)"
      using XBe3 by (simp add:algebra_simps power2_eq_square power3_eq_cube power_mult)
    hence 2: "(abs (U l X Y))^(2*nat X) * (abs (U l X Y^2*V w g Y) - 1)^(2*nat X) / (abs (U l X Y^2*V w g Y) - 1)^(3*nat X)
      = (abs (U l X Y))^(2*nat X) / (abs (U l X Y^2*V w g Y) - 1)^(nat X)"
      using of_int_mult frac_eq_eq abs_U2V_B2 B0 XBe3
      by (smt (z3) of_int_pos one_less_power zero_less_nat_eq)
    have "(abs (U l X Y))^(2*nat X) / (abs (U l X Y^2*V w g Y) - 1)^(nat X)
      = ( (abs (U l X Y))^2 / (abs (U l X Y^2*V w g Y) - 1) )^(nat X)"
      using B0 XBe3 abs_U2V_B2 of_int_power
      by (simp add: power_divide power_mult)
    hence 3: "abs (C l w h g Y X) / abs (K k l w g Y X)
      \<le> ( (abs (U l X Y))^2 / (abs (U l X Y^2*V w g Y) - 1) )^(nat X)"
      using 1 2 by simp
    have 4: "... \<le> (1 / 2)^(nat X)"
      using min_U2V XBe3 Power.linordered_semidom_class.power_mono
        [of "(abs (U l X Y))^2 / (abs (U l X Y^2*V w g Y) - 1)" "1/2" "nat X"] abs_U2V_B2
      by (smt (verit, ccfv_SIG) of_int_0_le_iff zero_le_divide_iff zero_le_power2)
    have 5: "(1/2)^(Suc n) \<le> (1/2::real)" for n::nat
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      note HR=this
      have "(1/2::real)^(Suc n) \<ge> (1/2::real)^(Suc (Suc n))" by simp
      then show ?case using HR order_trans by simp
    qed

    hence "abs (C l w h g Y X) / abs (K k l w g Y X) \<le> 1/2"
      using 3 4 XBe3 5[of "nat X-1"] order_trans
      by (smt (verit, del_insts) Suc_pred' zero_less_nat_eq)
    hence maj_CovK: "abs ( (C l w h g Y X) / (K k l w g Y X)) \<le> 1/2" by simp

    have "abs (2 * C l w h g Y X - 2 * L l Y * K k l w g Y X) < abs (K k l w g Y X)"
      using sat_f unfolding d2f_def
      using abs_le_square_iff linorder_not_less by blast
    hence "abs (2 * C l w h g Y X - 2 * L l Y * K k l w g Y X) / abs (K k l w g Y X) < 1" 
      using of_int_add by (smt (verit, ccfv_SIG) divide_less_eq_1 of_int_less_iff)
    hence "abs 2 * abs (C l w h g Y X - L l Y * K k l w g Y X) / abs (K k l w g Y X) < 1"
      using abs_mult[of "2::int" "C l w h g Y X - L l Y * K k l w g Y X"]
      by (metis Groups.mult_ac(1) int_distrib(4))
    hence "abs (C l w h g Y X - L l Y * K k l w g Y X) / abs (K k l w g Y X) < 1/2"
      by linarith
    hence 6: "abs ( (C l w h g Y X - L l Y * K k l w g Y X) / K k l w g Y X) < 1/2"
      using of_int_abs of_int_diff Fields.field_abs_sgn_class.abs_divide by simp
    have "real_of_int (C l w h g Y X - L l Y * K k l w g Y X) / real_of_int (K k l w g Y X)
      = real_of_int (C l w h g Y X) / real_of_int (K k l w g Y X) - real_of_int (L l Y) *
      real_of_int (K k l w g Y X) / real_of_int (K k l w g Y X)"
      using Fields.division_ring_class.diff_divide_distrib of_int_diff of_int_mult by metis
    hence "abs ( C l w h g Y X / K k l w g Y X - L l Y ) < 1/2"
      using min_K B0 6 by force
    hence maj_LmCovK: "abs (L l Y - C l w h g Y X / K k l w g Y X ) < 1/2"
      by linarith

    have "abs (L l Y) \<le> abs (L l Y - C l w h g Y X / (K k l w g Y X)) +
      abs ( (C l w h g Y X) / (K k l w g Y X))"
      using Groups.ordered_ab_group_add_abs_class.abs_triangle_ineq by linarith
    hence "abs (L l Y) < 1" using maj_LmCovK maj_CovK by linarith
    hence "l * Y = 0" unfolding L_def by simp
    then show ?thesis using assms abs_lBe1 by simp
  qed
  hence "R = X+1" using r_def by auto
  hence K_is_\<psi>U2V: "K k l w g Y X = \<psi>_int (U l X Y^2*V w g Y) (X+1)" using R_def by auto
  have "abs (U l X Y^2*V w g Y) = abs (U l X Y)* (abs (U l X Y) * abs (V w g Y))"
    using abs_mult[of "U l X Y^2" "V w g Y"] power2_eq_square[of "abs (U l x Y)"]
    apply simp
    using power2_eq_square by blast
  hence "abs (U l X Y^2*V w g Y) > abs (U l X Y) * 2"
    using mult_strict_left_mono[of 2 "abs (U l X Y) * abs (V w g Y)" "abs (U l X Y)"]
      absUBe2 absV_Be8 mult_strict_mono[of 1 "abs (U l X Y)" 2 "abs (V w g Y)"] by linarith
  hence "abs (U l X Y^2*V w g Y) > abs (2*X*(l*Y))*2" unfolding U_def L_def by auto
  hence "abs (U l X Y^2*V w g Y) > 4*X*(abs l * Y)"
    using abs_mult[of "2*X" "l*Y"] abs_mult[of 2 X] abs_mult[of l Y] assms(2) XBe3 by linarith
  hence U2V_B4X: "abs (U l X Y^2*V w g Y) > 4*X" using mult_strict_left_mono[of 1 "abs l * Y" "4*X"]
      mult_strict_mono[of 1 "abs l" 1 Y] assms(2) lx_nonzero XBe3 mult_left_mono[of 3 X 4]
    apply simp
    by (smt (z3) \<open>\<lbrakk>1 < \<bar>l\<bar> * Y; 0 < 4 * X\<rbrakk> \<Longrightarrow> 4 * X * 1 < 4 * X * (\<bar>l\<bar> * Y)\<close> pos_zmult_eq_1_iff zmult_zless_mono2)
  hence "abs (K k l w g Y X) = \<psi> (abs (U l X Y^2*V w g Y)) (nat (X+1))"
    using K_is_\<psi>U2V XBe3 eq_\<psi>_int[of "U l X Y^2*V w g Y" "X+1"] by auto
  hence K_nonzero: "K k l w g Y X \<noteq> 0"
    using lucas_monotone3[of "abs (U l X Y^2*V w g Y)" "nat (X+1)"] U2V_B4X XBe3 by auto
  have "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    = abs (\<psi>_int (A l w g Y X) (2*X+1) / \<psi>_int (U l X Y^2*V w g Y) (X+1))"
    using K_is_\<psi>U2V C_is_\<psi>BA B_def[of X] by auto
  hence "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    = abs (\<psi>_int (A l w g Y X) (2*X+1)) / abs (\<psi>_int (U l X Y^2*V w g Y) (X+1))" by auto
  hence eq_CoverK: "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    = \<psi> (abs (A l w g Y X)) (nat (2*X+1))/ \<psi> (abs (U l X Y^2*V w g Y)) (nat (X+1))"
    using eq_\<psi>_int XBe3 abs_U2V_B2 abs_A_Be16 by auto
  define \<rho> where "\<rho> = (abs (V w g Y)+1)^(2*nat X)/(abs (V w g Y))^(nat X)"
  have nat2X12X: "nat (2*X+1) = 2*nat X +1 \<and> nat (X+1) = nat X +1"
    using XBe3 by (auto simp add: algebra_simps)
  hence eq2_CoverK: "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    = \<psi> (abs (A l w g Y X)) (2*nat X+1)/ \<psi> (abs (U l X Y^2*V w g Y)) (nat X+1)"
    using eq_CoverK by auto

  have "e^2 < f^2 \<Longrightarrow> abs e < abs f" for e f::int
    by (smt (verit, del_insts) abs_if_raw abs_le_square_iff)
  hence "abs (2*C l w h g Y X - 2*L l Y * K k l w g Y X) < abs (K k l w g Y X)"
    using sat_f unfolding d2f_def by blast
  hence ineq1_CmLK: "abs (2*real_of_int (C l w h g Y X) - 2*real_of_int (L l Y) * K k l w g Y X)
    < abs (real_of_int (K k l w g Y X))"
    by (metis (no_types) of_int_abs of_int_diff of_int_less_iff of_int_mult of_int_numeral)
  have "2*real_of_int (K k l w g Y X) * (real_of_int (C l w h g Y X) / (K k l w g Y X) - real_of_int (L l Y))
    = 2*real_of_int (C l w h g Y X) - 2*real_of_int (L l Y) * K k l w g Y X"
    using K_nonzero distrib_left[of "2*real_of_int (K k l w g Y X)"
        "real_of_int (C l w h g Y X) / (K k l w g Y X)" "real_of_int (L l Y)"]
    by (auto simp add: algebra_simps)
  hence "abs (2*real_of_int (K k l w g Y X) * (real_of_int (C l w h g Y X) / (K k l w g Y X)
    - real_of_int (L l Y))) < abs (real_of_int (K k l w g Y X))"
    using ineq1_CmLK by presburger
  hence "abs (2*real_of_int (K k l w g Y X) * (real_of_int (C l w h g Y X) / (K k l w g Y X)
    - real_of_int (L l Y))) < abs (2*real_of_int (K k l w g Y X))/2" by argo
  hence "abs (2*real_of_int (K k l w g Y X)) * abs (real_of_int (C l w h g Y X) / (K k l w g Y X)
    - real_of_int (L l Y)) < abs (2*real_of_int (K k l w g Y X))* (1/2)"
    by (auto simp add: abs_mult)
  hence ineq2_CmLK: "abs (real_of_int (C l w h g Y X) / (K k l w g Y X) - real_of_int (L l Y)) < 1/2"
    using K_nonzero 
    using abs_ge_zero mult_less_cancel_left by blast
  have "e*f \<ge> 0 \<Longrightarrow> abs (e-f) < i \<Longrightarrow> abs e < abs f +i" for e f i::real by auto
  hence ineq3_CmLK: "abs (real_of_int (C l w h g Y X) / (K k l w g Y X)) < abs (real_of_int (L l Y)) + 1/2"
    using ineq2_CmLK by argo

  have \<psi>AB_is_pos: "\<psi> (abs (A l w g Y X)) (2*nat X+1) \<ge> (0::real)"
    using lucas_monotone3[of "abs (A l w g Y X)" "2*nat X +1"]XBe3 abs_A_Be16 U2V_B4X by auto
  have \<psi>U2V_is_pos: "\<psi> (abs (U l X Y^2*V w g Y)) (nat X+1) > (0::real)"
    using lucas_monotone3[of "abs (U l X Y^2*V w g Y)" "nat X +1"] XBe3 abs_A_Be16 U2V_B4X by auto
  have many_easy_ineq: "2*nat X - 1 + 1 = 2*nat X
    \<and> Suc (Suc (2*nat X - 1)) = 2*nat X +1 \<and> nat X - 2 + 2 = nat X
    \<and> Suc (Suc (Suc (nat X - 2))) = nat X +1 \<and> 1 < abs (A l w g Y X)
    \<and> 1 < abs ((U l X Y)\<^sup>2 * V w g Y)"
    using XBe3 abs_A_Be16 U2V_B4X by (auto simp add: algebra_simps)
  hence "\<psi> (abs (A l w g Y X)) (2*nat X+1) \<ge> (abs (A l w g Y X) - 1)^(2*nat X)
    \<and> \<psi> (abs (U l X Y^2*V w g Y)) (nat X+1) \<le> (abs (U l X Y^2*V w g Y))^(nat X)"
    using lucas_exp_growth_gt[of "abs (A l w g Y X)" "2*nat X - 1"]
      lucas_exp_growth_lt[of "abs (U l X Y^2*V w g Y)" "nat X-2"]
    by (simp add: lucas_exp_growth_gt[of "abs (A l w g Y X)" "2*nat X - 1"]
        lucas_exp_growth_lt[of "abs (U l X Y^2*V w g Y)" "nat X-2"])
  hence real_ineq_\<psi>: "real_of_int (\<psi> (abs (A l w g Y X)) (2*nat X+1)) \<ge> (abs (A l w g Y X) - 1)^(2*nat X)
    \<and> real_of_int (\<psi> (abs (U l X Y^2*V w g Y)) (nat X+1)) \<le> (abs (U l X Y^2*V w g Y))^(nat X)"
    by presburger

  have "abs (A l w g Y X) - 1 = real_of_int (abs (U l X Y))*abs (V w g Y +1) - abs (U l X Y)*(1/(abs (U l X Y)))"
    unfolding A_def using abs_mult absUBe2 by auto
  hence eqA: "abs (A l w g Y X) - 1 = abs (U l X Y)*(abs (V w g Y +1) - 1/abs (U l X Y))"
    using distrib_left[of "abs (U l X Y)" "abs (V w g Y+1)" "1/(abs (U l X Y))"]
    by (smt (verit, ccfv_SIG) ring_class.ring_distribs(1))
  have "real_of_int (\<psi> (abs (A l w g Y X)) (2*nat X+1)) \<ge> (real_of_int (abs (A l w g Y X) - 1))^(2*nat X)"
    by (metis real_ineq_\<psi> of_int_power_eq_of_int_cancel_iff)
  hence "\<psi> (abs (A l w g Y X)) (2*nat X+1) \<ge> (abs (U l X Y)*(abs (V w g Y +1) - 1/abs (U l X Y)))^(2*nat X)"
    using eqA by metis
  hence other_ineq_\<psi>AB: "\<psi> (abs (A l w g Y X)) (2*nat X+1) \<ge> (abs (U l X Y))^(2*nat X)*(abs (V w g Y +1)
    - 1/abs (U l X Y))^(2*nat X)" 
    using power_mult_distrib[of "abs (U l X Y)" "abs (V w g Y +1) - 1/abs (U l X Y)" "2*nat X"]
    by auto
  have "1/abs (U l X Y) \<le> 1" using absUBe2 divide_le_eq_1_pos by auto
  hence "abs (V w g Y +1) - 1/abs (U l X Y) \<ge> abs (V w g Y) - 2" by linarith
  hence several_pow_pos: "(abs (V w g Y +1) - 1/abs (U l X Y))^(2*nat X) \<ge> (abs (V w g Y) - 2)^(2*nat X)
    \<and> (abs (U l X Y))^(2*nat X) > 0 \<and> (abs (V w g Y) - 2)^(2*nat X) \<ge> 0"
    using power_mono[of "abs (V w g Y) - 2" "abs (V w g Y +1) - 1/abs (U l X Y)" "2*nat X"] absV_Be8
    by (smt (z3) absUBe2 of_int_1_le_iff of_int_power zero_less_power)
  hence other_ineq_\<psi>AB_2: "real_of_int (\<psi> (abs (A l w g Y X)) (2*nat X+1))
    \<ge> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((abs (V w g Y) - 2)^(2*nat X))"
    using other_ineq_\<psi>AB mult_left_mono[of "real_of_int (abs (V w g Y) - 2)^(2*nat X)"
        "(abs (V w g Y +1) - 1/abs (U l X Y))^(2*nat X)" "real_of_int (abs (U l X Y))^(2*nat X)"]
    by (smt (z3) of_int_power zero_le_even_power')

  have "real_of_int (\<psi> (abs (U l X Y^2*V w g Y)) (nat X+1)) \<le> (abs (U l X Y^2)*abs (V w g Y))^(nat X)"
    using abs_mult[of "U l X Y^2" "V w g Y"] real_ineq_\<psi> by auto
  hence "real_of_int (\<psi> (abs (U l X Y^2*V w g Y)) (nat X +1))
    \<le> (abs (U l X Y^2))^(nat X)*abs (V w g Y)^(nat X)"
    using power_mult_distrib[of "abs (U l X Y^2)" "abs (V w g Y)" "nat X"] by metis
  hence "real_of_int (\<psi> (abs (U l X Y^2*V w g Y)) (nat X +1))
    \<le> (abs (U l X Y)^2)^(nat X)*abs (V w g Y)^(nat X)"
    by auto
  hence "real_of_int (\<psi> (abs (U l X Y^2*V w g Y)) (nat X +1))
    \<le> (abs (U l X Y))^(2*nat X)*abs (V w g Y)^(nat X)"
    using power_mult[of "abs (U l X Y)" 2 "nat X"] by auto
  hence ineq_\<psi>U2V: "real_of_int (\<psi> (abs (U l X Y^2*V w g Y)) (nat X +1))
    \<le> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int ((abs (V w g Y))^(nat X))" by auto
  hence "\<psi> (abs (A l w g Y X)) (2*nat X+1) / \<psi> (abs (U l X Y^2*V w g Y)) (nat X+1)
    \<ge> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((abs (V w g Y) - 2)^(2*nat X))
    / (real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int ((abs (V w g Y))^(nat X)))"
    using \<psi>AB_is_pos \<psi>U2V_is_pos other_ineq_\<psi>AB_2 frac_le
      [of "\<psi> (abs (A l w g Y X)) (2*nat X+1)"
        "real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((abs (V w g Y) - 2)^(2*nat X))"
        "\<psi> (abs (U l X Y^2*V w g Y)) (nat X+1)"
        "real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int ((abs (V w g Y))^(nat X))"]
    by auto
  hence "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    \<ge> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((abs (V w g Y) - 2)^(2*nat X))
    / (real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int ((abs (V w g Y))^(nat X)))"
    using eq2_CoverK by auto
  hence "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    \<ge> real_of_int((abs (V w g Y) - 2)^(2*nat X)) / real_of_int ((abs (V w g Y))^(nat X))"
    using several_pow_pos by auto
  hence "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    \<ge> real_of_int(((abs (V w g Y) - 2)^2)^(nat X)) / real_of_int ((abs (V w g Y))^(nat X))"
    using power_mult[of "abs (V w g Y) - 2" 2 "nat X"] by auto
  hence "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    \<ge> (real_of_int((abs (V w g Y) - 2)^2))^(nat X) / (real_of_int (abs (V w g Y)))^(nat X)" by auto
  hence ineq_CoverK_1: "abs (real_of_int (C l w h g Y X) /(K k l w g Y X))
    \<ge> ((real_of_int((abs (V w g Y) - 2)^2)) / (real_of_int (abs (V w g Y))))^(nat X)"
    by (metis power_divide)

  have "(abs (V w g Y)-2)^2 \<ge> abs (V w g Y)*abs (V w g Y) - 4*abs (V w g Y)"
    using power2_diff[of "abs (V w g Y)" 2] power2_eq_square[of "V w g Y"] by auto
  hence "2*(abs (V w g Y) - 2)^2 \<ge> abs (V w g Y)*abs (V w g Y) + abs (V w g Y)*abs(V w g Y) - 8*abs (V w g Y)"
    by auto
  hence "2*(abs (V w g Y)-2)^2 \<ge> abs (V w g Y)*abs (V w g Y) - abs (V w g Y)"
    using absV_Be8 mult_right_mono[of 7 "abs (V w g Y)" "abs (V w g Y)"] by force
  hence "2*(abs (V w g Y)-2)^2 \<ge> abs (V w g Y)*(abs (V w g Y) - 1)"
    by (auto simp add: algebra_simps)
  hence ineq_absVm2: "2*real_of_int ((abs (V w g Y)-2)^2)
    \<ge> real_of_int (abs (V w g Y))*real_of_int (abs (V w g Y)-1)"
    by (metis of_int_le_iff of_int_mult of_int_numeral)
  have "(2*real_of_int ((abs (V w g Y)-2)^2))/(2*abs (V w g Y)) = (real_of_int((abs (V w g Y) - 2)^2))
    / (real_of_int (abs (V w g Y))) \<and> (real_of_int (abs (V w g Y))*real_of_int (abs (V w g Y)-1))
    /(2*abs (V w g Y)) = (abs (V w g Y) - 1)/2" using absV_Be8 by auto
  hence "(real_of_int((abs (V w g Y) - 2)^2)) / (real_of_int (abs (V w g Y))) \<ge> (abs (V w g Y) - 1)/2" 
    using ineq_absVm2 divide_right_mono[of "abs (V w g Y)*(abs (V w g Y) - 1)" "2*(abs (V w g Y)-2)^2"
        "2*abs (V w g Y)"]
        absV_Be8 divide_right_mono of_int_0 of_int_power_le_of_int_cancel_iff zero_power2 by auto
  hence "((real_of_int((abs (V w g Y) - 2)^2)) / (real_of_int (abs (V w g Y))))^(nat X)
    \<ge> ((abs (V w g Y) - 1)/2)^(nat X)"
    using power_mono[of "(abs (V w g Y) - 1)/2"
          "(real_of_int((abs (V w g Y) - 2)^2)) / (real_of_int (abs (V w g Y)))" "nat X"] absV_Be8
    by auto
  hence  "abs (real_of_int (C l w h g Y X) /(K k l w g Y X)) \<ge> ((abs (V w g Y) - 1)/2)^(nat X)"
    using ineq_CoverK_1 by auto
  hence ineq_L_Vm1: "abs (real_of_int (L l Y)) + 1/2 \<ge> ((abs (V w g Y) - 1)/2)^(nat X)"
    using ineq3_CmLK by auto
  have "(abs (V w g Y) - 1)/2 \<ge> 2" using absV_Be8 by auto
  hence "((abs (V w g Y) - 1)/2)^(nat X) \<ge> 2" using power_mono[of 2 "(abs (V w g Y) - 1)/2" "nat X"]
 power_increasing_iff[of 2 1 "nat X"] XBe3 by (smt (verit) self_le_power zero_less_nat_eq)
  hence "((abs (V w g Y) - 1)/2)^(nat X) > 1/2*((abs (V w g Y) - 1)/2)^(nat X)+1/2" by auto
  hence "abs (real_of_int (L l Y)) > 1/2*((abs (V w g Y) - 1)/2)^(nat X)"
    using ineq_L_Vm1 by linarith
  hence "2*abs (real_of_int (L l Y)) > ((abs (V w g Y)-1)/2)^(nat X)" by auto
  hence ineq_L_Vm1_2: "2*abs (L l Y) > ((abs (V w g Y)-1)/2)^(nat X)" by auto
  have "real_of_int X*(abs (V w g Y)-1) \<ge> (abs (V w g Y)-1)"
    using XBe3 absV_Be8 mult_right_mono[of 1 "real_of_int X" "abs (V w g Y)-1"] of_int_1_le_iff
    by auto
  hence "X*(abs (V w g Y)-1) > (abs (V w g Y)-1)/2" using absV_Be8 by auto

  hence "2*abs (L l Y)*real_of_int (X*(abs (V w g Y) - 1))
    > ((abs (V w g Y) - 1)/2)^(nat X)* ((abs (V w g Y) - 1)/2)" using XBe3 absV_Be8 mult_strict_mono
    [of "((abs (V w g Y) - 1)/2)^(nat X)" "2*abs (L l Y)" "(abs (V w g Y)-1)/2" "X*(abs (V w g Y) - 1)"]
    ineq_L_Vm1_2 absL_Be1 by auto
  hence "2*abs (L l Y)*real_of_int (X*(abs (V w g Y) - 1)) > ((abs (V w g Y) - 1)/2)^(nat X + 1)"
    using power_add[of "(abs (V w g Y) - 1)/2" "nat X" 1] by (metis power_one_right)
  hence "2*abs (L l Y)*X*(abs (V w g Y) - 1) > ((abs (V w g Y) - 1)/2)^(nat X + 1)" by auto
  hence "2*abs (L l Y)*X*abs (V w g Y + 1) > ((abs (V w g Y) - 1)/2)^(nat X + 1)" using XBe3
      mult_left_mono[of "abs (V w g Y) - 1" "abs (V w g Y + 1)" "2*abs (L l Y)*X"]
    by (smt (z3) nat_0_iff nat_abs_mult_distrib nat_mult_distrib of_int_less_iff)
  hence "abs (2*L l Y * X*(V w g Y + 1)) > ((abs (V w g Y) - 1)/2)^(nat X + 1)"
    using XBe3 by (auto simp add: abs_mult)
  hence absA_B_Vm1: "abs (A l w g Y X) > ((abs (V w g Y) - 1)/2)^(nat X + 1)"
    unfolding A_def U_def by (auto simp add: algebra_simps)

  have "abs (V w g Y) - 1 = 4* abs w *g*Y - 1"
    unfolding V_def using assms by (auto simp add: abs_mult)
  hence "abs (V w g Y)-1 \<ge> 2*abs w * g * Y"
    using mult_mono[of 2 "4*abs w *g" 1 Y] mult_mono[of 2 "4*abs w" 1 g] mult_mono[of 2 4 1 "abs w"]
    assms w_nonzero by auto
  hence "real_of_int (abs (V w g Y) - 1) \<ge> 2*abs w * g * Y" by presburger
  hence ineq_Vm1_wgY: "(abs (V w g Y)-1)/2 \<ge> abs w * g * Y"
    using divide_right_mono[of "2*abs w * g * Y" "abs (V w g Y) - 1" 2] by auto
  have "abs w * g * Y \<ge> abs w * b"
    using assms mult_mono[of "abs w" "abs w * g" b Y] mult_left_mono[of 1 g "abs w"] by auto
  hence "abs w * g * Y \<ge> abs (W w b)"
    unfolding W_def using assms abs_mult[of w b] by (auto simp add: algebra_simps)
  hence "(abs (V w g Y)-1)/2 \<ge> abs (W w b)" using ineq_Vm1_wgY by linarith
  hence "real_of_int (abs (A l w g Y X)) > (abs (W w b))^(nat X + 1)"
    using power_mono[of "abs (W w b)" "(abs (V w g Y)-1)/2" "nat X +1"] absA_B_Vm1 by auto
  hence "abs (A l w g Y X) > (abs (W w b))^(nat X + 1)" by presburger
  hence "abs (A l w g Y X) > (abs (W w b))^(nat X + 1) \<and> nat X +1 \<ge> 4 \<and> abs (W w b) \<ge> 1"
    using XBe3 W_nonzero by auto 
  hence "abs (A l w g Y X) > (abs (W w b))^(4)"
    using power_increasing[of 4 "nat X +1" "abs (W w b)"] by auto
  hence A_B_W4: "abs (A l w g Y X) > (W w b)^4" by auto

  have "abs w * g * Y \<ge> 2^8" using mult_mono[of 1 "abs w*g" "2^8" Y] mult_mono[of 1 "abs w" 1 g]
      w_nonzero assms by auto
  hence "real_of_int (abs w * g * Y) \<ge> 2^8" using numeral_power_le_of_int_cancel_iff by blast
  hence "(abs (V w g Y)-1)/2 \<ge> 2^8" using ineq_Vm1_wgY by auto
  hence "real_of_int (abs (A l w g Y X)) > (2^8)^(nat X + 1)"
    using power_mono[of "2^8" "(abs (V w g Y)-1)/2" "nat X +1"] absA_B_Vm1 by auto
  hence "abs (A l w g Y X) > (2^8)^(nat X + 1)"
    by (metis of_int_less_iff of_int_numeral of_int_power)
  hence "abs (A l w g Y X) > 2^(8*(nat X +1))"
    using power_mult[of 2 8 "nat X +1"] by metis
  hence "abs (A l w g Y X) > 2^(8*(nat X +1)) \<and> 4*nat (B X) \<le> 8*(nat X +1)"
    unfolding B_def using XBe3 by auto
  hence A_B_2po4B: "abs (A l w g Y X) > 2^(4*nat (B X))"
    using power_increasing[of "4*nat (B X)" "8*(nat X +1)" 2]
    by (smt (verit, ccfv_SIG))

  have "(3*W w b*C l w h g Y X - 2*((W w b)^2 - 1)) mod (2*A l w g Y X - 5) = 0 mod (2*A l w g Y X - 5)"
    using sat_c unfolding d2c_def S_def T_def by auto
  hence "3*W w b*\<psi> (A l w g Y X) (nat (B X)) mod (2*A l w g Y X - 5) = 2*((W w b)^2 - 1) mod (2*A l w g Y X - 5)"
    using C_is_\<psi>BA mod_add_cong[of "3*W w b*C l w h g Y X - 2*((W w b)^2 - 1)" "2*A l w g Y X - 5"
        0 "2*((W w b)^2 - 1)" "2*((W w b)^2 - 1)"] \<psi>_int_def[of "A l w g Y X" "B X"] B_Be7 by auto
  hence "W w b = 2^(nat (B X))"
    using lucas_diophantine_rec[of "nat (B X)" "W w b" "A l w g Y X"] A_B_W4 A_B_2po4B B_Be7 by auto
  hence bw_pos: "b*w = 2^(nat (B X)) \<and> w > 0 \<and> b > 0" unfolding W_def using assms
    by (metis nat_0_iff nat_less_eq_zless not_less0 zero_le_mult_iff zero_le_square zero_less_mult_iff zero_less_numeral zero_less_power)
  hence "nat b*nat w = 2^(nat (B X))" by (metis b_def nat_eq_numeral_power_cancel_iff nat_mult_distrib)
  hence is_power2_b: "is_power2 (nat b)" unfolding is_power2_def
    using prime_power_mult_nat[of 2 "nat b" "nat w" "nat (B X)"] two_is_prime_nat by auto

  have "V w g Y \<ge> 4*w*g*b" unfolding V_def using mult_left_mono[of b Y "4*w*g"] bw_pos assms by auto
  hence "V w g Y \<ge> 4*(b*w)*g" by (auto simp add: algebra_simps)
  hence "V w g Y \<ge> 4*2^(nat (B X))*g" using bw_pos by auto
  hence "V w g Y \<ge> 4*2^(nat (B X))*g \<and> (4::int)*2^(nat (B X)) \<ge> 0" using zero_less_power[of 2 "nat (B X)"]
 zero_less_mult_iff[of 4 "2^(nat (B X))"] by simp
  hence "V w g Y \<ge> 4*2^(nat (B X))" using mult_left_mono[of 1 g "4*2^(nat (B X))"] assms by presburger
  hence "V w g Y \<ge> 4*2^(2*nat X +1)"
    unfolding B_def by (simp add: \<open>nat (2 * X + 1) = 2 * nat X + 1 \<and> nat (X + 1) = nat X + 1\<close>)
  hence V_Be82is_power2X: "V w g Y \<ge> 8*2^(2*nat X)" by (simp add: power_add)
  hence VBe8: "V w g Y \<ge> 8"
    using \<open>4 * 2 ^ nat (B X) * g \<le> V w g Y \<and> 0 \<le> 4 * 2 ^ nat (B X)\<close> \<open>4 * 2 ^ nat (B X) \<le> V w g Y\<close> absV_Be8
    by linarith

  define \<rho> where "\<rho> = (V w g Y +1)^(2*nat X)/(V w g Y)^(nat X)"
  have "\<rho> = (\<Sum>i\<le>2*nat X. (2*nat X choose i)*V w g Y^i)/(V w g Y)^(nat X)" unfolding \<rho>_def
    using binomial_ring[of "V w g Y" 1 "2*nat X"] by auto
  hence "\<rho> = (\<Sum>i\<le>2*nat X. (2*nat X choose (nat (int i)))*V w g Y^(nat (int i)))/(V w g Y)^(nat X)"
    by auto
  hence "\<rho> = (sum (\<lambda>i. (2*nat X choose nat i)*V w g Y ^(nat i)) (set[0..int (2*nat X)]))/(V w g Y)^(nat X)" 
    using change_sum[of "\<lambda>i. (2*nat X choose (nat i))*V w g Y^(nat i)" "2*nat X"] by presburger
  hence "\<rho> = (sum (\<lambda>i. (2*nat X choose nat i)*V w g Y ^(nat i)) (set[0..2*X]))/(V w g Y)^(nat X)"
    using XBe3 by auto
  hence "\<rho> = (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i)) (set[0..2*X]))/(V w g Y)^(nat X)"
    by auto
  hence \<rho>_binom1: "\<rho> = (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X))
    (set[0..2*X]))"
    using sum_divide_distrib by blast
  have "(set[0..2*X]) = (set[0..X-1]) \<union> (set[X..2*X]) \<and> (set[0..X-1]) \<inter> (set[X..2*X]) = {}
    \<and> finite (set[0..X-1]) \<and> finite (set[0..2*X])" by auto
  hence \<rho>_binom2: "\<rho> = (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[0..X-1]))
    + (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X..2*X]))"
    using \<rho>_binom1 by (auto simp add: sum.union_disjoint)
  have "i\<in> (set[0..X-1]) \<Longrightarrow> real_of_int (V w g Y ^(nat i)) /(V w g Y)^(nat X)
    = 1/(V w g Y) * 1/(V w g Y)^(nat (X - i - 1))" for i
  proof -
    fix i
    assume hyp: "i\<in> (set[0..X-1])"
    have fact1: "real_of_int (V w g Y ^(nat i))*(V w g Y)^(nat X - nat i) = (V w g Y)^(nat X)"
      using power_add[of "V w g Y" "nat i" "nat X - nat i"] XBe3 hyp
      apply simp
      by (metis add_diff_inverse_nat less_SucI nat_less_eq_zless not_less_eq power_add)
    have "Suc (nat (X - i - 1)) = nat X - nat i" using hyp by (auto simp add: algebra_simps)
    hence "(V w g Y)^(nat i)*real_of_int (V w g Y) * (V w g Y)^(nat (X - i - 1)) = (V w g Y)^(nat X)"
      using power_Suc[of "V w g Y" "nat X - nat i - 1"] hyp XBe3 fact1
      apply simp
      by (metis (no_types) Nat.add_0_right \<open>Suc (nat (X - i - 1)) = nat X - nat i\<close>
          left_add_mult_distrib power_0 power_Suc power_add power_one_right)
    hence eq1: "(V w g Y)^(nat i)*real_of_int (V w g Y) * (V w g Y)^(nat (X - i - 1))
      /((V w g Y)^(nat X)*real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1)))
      = (V w g Y)^(nat X) / ((V w g Y)^(nat X)*real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1)))"
      by auto
    have "(V w g Y)^(nat X) / ((V w g Y)^(nat X)*real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1))) 
      = (V w g Y)^(nat X) / ((V w g Y)^(nat X)*(real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1))))"
      using absV_Be8 by (auto simp add: algebra_simps)
    have triv_simp: "a \<noteq> 0 \<Longrightarrow> a/(a*c) = (1::real)/c" for a c by simp
    hence eq2: "(V w g Y)^(nat X) / ((V w g Y)^(nat X)*real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1)))
      = 1 / (real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1)))" using absV_Be8 triv_simp[of "(V w g Y)^(nat X)"
      "real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1))"] by auto
    hence "(V w g Y)^(nat X) / ((V w g Y)^(nat X)*real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1))) 
      = 1 / (real_of_int (V w g Y))* 1/(V w g Y)^(nat (X - i - 1))" by auto
    have "(V w g Y)^(nat i)*real_of_int (V w g Y) * (V w g Y)^(nat (X - i - 1))/((V w g Y)^(nat X)
      *real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1)))
      = (V w g Y)^(nat i)*(real_of_int (V w g Y) * (V w g Y)^(nat (X - i - 1))/(real_of_int (V w g Y)
      *(V w g Y)^(nat (X - i - 1))*(V w g Y)^(nat X)))"
      by (auto simp add: algebra_simps)
    hence "(V w g Y)^(nat i)*real_of_int (V w g Y) * (V w g Y)^(nat (X - i - 1))/((V w g Y)^(nat X)
      *real_of_int (V w g Y)*(V w g Y)^(nat (X - i - 1)))
      = (V w g Y)^(nat i)/((V w g Y)^(nat X))"
      using triv_simp[of "real_of_int (V w g Y) * (V w g Y)^(nat (X - i - 1))" "(V w g Y)^(nat X)"]
        absV_Be8 by auto
    thus "real_of_int (V w g Y ^(nat i)) /(V w g Y)^(nat X) = 1/(real_of_int (V w g Y))*1/(V w g Y)^(nat (X - i - 1))"
      using eq1 eq2 by auto
  qed
  hence "i\<in> (set[0..X-1]) \<Longrightarrow> real (2*nat X choose nat i)*(V w g Y ^(nat i) /(V w g Y)^(nat X)) 
    = real (2*nat X choose nat i) *(1/(real_of_int (V w g Y))*1/(V w g Y)^(nat (X - i - 1)))" for i
    by auto
  hence "i\<in> (set[0..X-1]) \<Longrightarrow> real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X) 
    = real (2*nat X choose nat i) *1/(real_of_int (V w g Y))*1/(V w g Y)^(nat (X - i - 1))" for i
    by (auto simp add: algebra_simps)
  hence "\<rho> = (sum (\<lambda>i. real (2*nat X choose nat i) *1/(real_of_int (V w g Y))*1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    + (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X..2*X]))"
    using \<rho>_binom2 by auto
  hence "\<rho> = (sum (\<lambda>i. 1/(real_of_int (V w g Y))*(real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1)))) (set[0..X-1]))
    + (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X..2*X]))"
    by (auto simp add: algebra_simps)
  hence \<rho>_binom3: "\<rho> = 1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    + (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X..2*X]))" 
    using sum_distrib_left[of "1/(real_of_int (V w g Y))" "\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))"
        "set[0..X-1]"] by auto
  have "set[X..2*X] = {X}\<union>(set[X+1..2*X]) \<and> {X}\<inter>(set[X+1..2*X]) = {} \<and> finite {X} \<and> finite (set[X+1..2*X])"
    using XBe3 by auto
  hence "\<rho> = 1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    + real (2*nat X choose nat X)*V w g Y ^(nat X) /(V w g Y)^(nat X) + (sum (\<lambda>i. real (2*nat X choose nat i)
    * V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X+1..2*X]))"
    using \<rho>_binom3 sum.union_disjoint[of "{X}" "set[X+1..2*X]"
        "\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)"] by auto
  hence \<rho>_binom4: "\<rho> = 1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    + real (2*nat X choose nat X) + (sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X+1..2*X]))"
    using absV_Be8 by auto

  have invV_pos: "1/(real_of_int (V w g Y)) \<ge> 0" using VBe8 by auto
  have binom_is_pos: "i\<in>(set[0..X-1])\<union>(set[0..2*X]) \<Longrightarrow> real (2*nat X choose nat i) \<ge> 0" for i
    using of_nat_0_le_iff by blast
  have "i\<in> (set[0..X-1]) \<Longrightarrow> 1/(V w g Y)^(nat (X - i - 1)) \<ge> 0" for i using VBe8 by force
  hence "i\<in> (set[0..X-1]) \<Longrightarrow> real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1)) \<ge> 0" for i
    using binom_is_pos by simp
  hence Vfrac_\<rho>_pos: "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1])) \<ge> 0"
    using sum_nonneg[of "set[0..X-1]" "\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))"]
    by simp
  hence frac_\<rho>_pos: "1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i)
    * 1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1])) \<ge> 0"
    using invV_pos by simp

  have obv_pos: "1/(8::real)*1/2^(nat (2*X)) > 0" by force
  have "2*nat X = nat (2*X)" using XBe3 by (auto simp add: algebra_simps)
  hence "2*X > X-1 \<and> X-1 > 0 \<and> 2*X \<ge> 0 \<and> real (2*nat X choose nat (2*X)) = 1" using XBe3 by auto
  hence "2*X\<in>(set[0..2*X]) \<and> 2*X\<notin>(set[0..X-1]) \<and> real (2*nat X choose nat (2*X)) > 0
    \<and> set[0..X-1] \<subseteq> set[0..2*X]" by auto
  hence ineq_will_be_strict: "2*X \<in> (set[0..2*X])-(set[0..X-1]) \<and> real (2*nat X choose nat (2*X)) > 0
    \<and> finite (set[0..2*X]) \<and> set[0..X-1]\<subseteq>set[0..2*X]" using XBe3 Diff_iff[of "2*X" "set[0..2*X]" "set[0..X-1]"]
    by blast
  have "i\<in>(set[0..X-1]) \<Longrightarrow> (V w g Y)^(nat (X - i - 1)) \<ge> 1" for i using VBe8 by force
  hence "i\<in>(set[0..X-1]) \<Longrightarrow> 1/real_of_int ((V w g Y)^(nat (X-i-1))) \<le> 1" for i
    by (smt (verit, del_insts) divide_right_mono divide_self of_int_1_le_iff)
  hence "i\<in>(set[0..X-1]) \<Longrightarrow> real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1)) \<le> real (2*nat X choose nat i)" for i
    using binom_is_pos mult_left_mono[of "1/(V w g Y)^(nat (X - i - 1))" 1 "real (2*nat X choose nat i)"]
    by simp
  hence "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    \<le> (sum (\<lambda>i. real (2*nat X choose nat i))) (set[0..X-1])" using sum_mono[of "set[0..X-1]"
    "\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))" "\<lambda>i. real (2*nat X choose nat i)"]
    by auto
  hence "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < (sum (\<lambda>i. real (2*nat X choose nat i))) (set[0..2*X])" using sum_strict_mono2[of "set[0..2*X]"
    "set[0..X-1]" "2*X" "\<lambda>i. real (2*nat X choose nat i)"] ineq_will_be_strict binom_is_pos by simp
  hence "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < real_of_int ((sum (\<lambda>i. int (2*nat X choose nat i))) (set[0..2*X]))" by simp
  hence "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < real_of_int (\<Sum>i\<le>nat(2*X). int (2*nat X choose i))"
    using change_sum[of "\<lambda>i. int (2*nat X choose nat i)" "nat (2*X)"] XBe3 by auto
  hence hello: "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < real (\<Sum>i\<le>nat(2*X). 2*nat X choose i) \<and> 2*nat X = nat (2*X)"
    by auto
  hence "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < real (\<Sum>i\<le>nat(2*X). nat (2*X) choose i)"
    by auto
  hence "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < real ((1+1)^(nat (2*X)))" using binomial[of 1 1 "nat (2*X)"]
    by auto
  hence sum_coeff_binom: "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < 2^(nat (2*X))"
    by auto
  have "8*2^(2*nat X)\<le>real_of_int (V w g Y)" using V_Be82is_power2X
    by (metis (mono_tags) numeral_power_eq_of_int_cancel_iff of_int_le_iff of_int_mult of_int_numeral)
  hence "1/(real_of_int (V w g Y)) \<le> 1/(8*2^(2*nat (X)))"
    using V_Be82is_power2X using inv_decr[of "8*2^(2*nat X)" "real_of_int (V w g Y)"] by simp
  hence "1/(real_of_int (V w g Y)) \<le> 1/8*1/2^(2*nat (X))" by auto
  hence "1/(real_of_int (V w g Y)) \<le> 1/8*1/2^(nat (2*X))" using hello by auto
  hence "1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < (1/8*1/2^(nat(2*X)))*2^(nat(2*X))" 
    using sum_coeff_binom Vfrac_\<rho>_pos obv_pos mult_strict_mono[of "1/(real_of_int (V w g Y))" "1/8*1/2^(nat (2*X))"
        "(sum (\<lambda>i. real (2*nat X choose nat i) *1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))" "2^(nat (2*X))"]
    by fastforce
  hence frac_\<rho>_L8: "1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i) * 1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))
    < 1/8" using divide_self[of "2^(nat(2*X))"] by auto

  have "i\<in>set[X+1..2*X] \<Longrightarrow> real_of_int (V w g Y) ^(nat i) /(real_of_int (V w g Y))^(nat X)
    = V w g Y * real_of_int (V w g Y) ^(nat i - nat X - 1)" for i
    using VBe8 div_pow[of "nat X" "nat i" "real_of_int (V w g Y)"] by auto
  hence "i\<in>set[X+1..2*X] \<Longrightarrow> V w g Y ^(nat i) /(V w g Y)^(nat X)
    = V w g Y * real_of_int (V w g Y) ^(nat i - nat X - 1)" for i by auto
  hence "i\<in>set[X+1..2*X] \<Longrightarrow> real (2*nat X choose nat i)*(V w g Y ^(nat i) /(V w g Y)^(nat X))
    = V w g Y*(real (2*nat X choose nat i)*V w g Y ^(nat i - nat X - 1))" for i
    by (auto simp add: algebra_simps)
  hence "(sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X+1..2*X]))
    = (sum (\<lambda>i. V w g Y*(real (2*nat X choose nat i)*V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))"
    by auto
  hence "(sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X+1..2*X]))
    = V w g Y*(sum (\<lambda>i. (real (2*nat X choose nat i)*V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))"
    by (auto simp add: sum_distrib_left)
  hence "(sum (\<lambda>i. real (2*nat X choose nat i)*V w g Y ^(nat i) /(V w g Y)^(nat X)) (set[X+1..2*X]))
    = V w g Y*(sum (\<lambda>i. (int (2*nat X choose nat i)*V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))"
    by auto
  hence \<rho>_binom5: "\<rho> = 1/(real_of_int (V w g Y))*(sum (\<lambda>i. real (2*nat X choose nat i)
    * 1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1])) + real (2*nat X choose nat X)
    + V w g Y*(sum (\<lambda>i. (int (2*nat X choose nat i)*V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))"
    using \<rho>_binom4 by auto

  define \<rho>_int where "\<rho>_int = int (2*nat X choose nat X) 
    + V w g Y*(sum (\<lambda>i. (int (2*nat X choose nat i) * V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))"
  define \<rho>_frac where "\<rho>_frac = 1/(real_of_int (V w g Y))
    * (sum (\<lambda>i. real (2*nat X choose nat i) * 1/(V w g Y)^(nat (X - i - 1))) (set[0..X-1]))"
  have \<rho>_is_intpfrac: "\<rho> = \<rho>_int + \<rho>_frac" using \<rho>_binom5 \<rho>_int_def \<rho>_frac_def by simp
  have ineq_\<rho>_frac: "0 \<le> \<rho>_frac \<and> \<rho>_frac < 1/8" using frac_\<rho>_L8 frac_\<rho>_pos \<rho>_frac_def by simp
  hence getting_int: "abs (real_of_int q - \<rho>) < 1-1/8 \<Longrightarrow> q = \<rho>_int" for q::int
  proof -
    assume hyp: "abs (real_of_int q - \<rho>) < 1-1/8"
    have "abs (real_of_int q - real_of_int \<rho>_int) \<le> abs (real_of_int q - \<rho>) + abs (\<rho> - \<rho>_int)"
      by auto
    hence "abs (real_of_int q - real_of_int \<rho>_int) < 1 - 1/8 + abs \<rho>_frac" using hyp \<rho>_is_intpfrac
      by auto
    hence "abs (real_of_int q - real_of_int \<rho>_int) < 1" using ineq_\<rho>_frac by auto
    thus ?thesis by linarith
  qed

  have "Y dvd V w g Y" unfolding V_def by auto
  hence "Y dvd V w g Y*(sum (\<lambda>i. (int (2*nat X choose nat i) *
    V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))" by auto
  hence Y_dvd_iff: "Y dvd (int (2*nat X choose nat X)) = (Y dvd \<rho>_int)" unfolding \<rho>_int_def
    using dvd_add_right_iff[of Y "V w g Y*(sum (\<lambda>i. (int (2*nat X choose nat i)
      *V w g Y ^(nat i - nat X - 1))) (set[X+1..2*X]))" "int (2*nat X choose nat X)"] by presburger

    have "abs (2 * C l w h g Y X - 2 * L l Y * K k l w g Y X) < abs (K k l w g Y X)"
      using sat_f unfolding d2f_def
      using abs_le_square_iff linorder_not_less by blast
    hence "abs (2 * C l w h g Y X - 2 * L l Y * K k l w g Y X) / abs (K k l w g Y X) < 1" 
      using of_int_add by (smt (verit, ccfv_SIG) divide_less_eq_1 of_int_less_iff)
    hence "abs 2 * abs (C l w h g Y X - L l Y * K k l w g Y X) / abs (K k l w g Y X) < 1"
      using abs_mult[of "2::int" "C l w h g Y X - L l Y * K k l w g Y X"]
      by (metis Groups.mult_ac(1) int_distrib(4))
    hence "abs (C l w h g Y X - L l Y * K k l w g Y X) / abs (K k l w g Y X) < 1/2"
      by linarith
    hence 6: "abs ( (C l w h g Y X - L l Y * K k l w g Y X) / K k l w g Y X) < 1/2"
      using of_int_abs of_int_diff Fields.field_abs_sgn_class.abs_divide by simp
    have "real_of_int (C l w h g Y X - L l Y * K k l w g Y X) / real_of_int (K k l w g Y X) 
      = real_of_int (C l w h g Y X) / real_of_int (K k l w g Y X) - real_of_int (L l Y)
      * real_of_int (K k l w g Y X) / real_of_int (K k l w g Y X)"
      using Fields.division_ring_class.diff_divide_distrib of_int_diff of_int_mult by metis
    hence "abs ( C l w h g Y X / K k l w g Y X - L l Y ) < 1/2"
      using K_nonzero 6 by force
    hence maj_LmCovK: "abs (L l Y - C l w h g Y X / K k l w g Y X ) < 1/2"
      by linarith

  have "abs (\<rho> - (real_of_int (C l w h g Y X))/(K k l w g Y X)) \<le> 1 - 1/8 - 1/2 \<Longrightarrow> \<rho>_int = L l Y"
  proof -
    assume hyp: "abs (\<rho> -  (real_of_int (C l w h g Y X))/(K k l w g Y X)) \<le> 1 - 1/8 - 1/2"
    have "abs (\<rho> - L l Y) \<le> abs (\<rho> -  (real_of_int (C l w h g Y X))/(K k l w g Y X))
      + abs ((real_of_int (C l w h g Y X))/(K k l w g Y X) - L l Y)" by auto
    hence "abs (\<rho> - L l Y) < 1 - 1/8" using maj_LmCovK hyp by argo
    thus "\<rho>_int = L l Y" using getting_int[of "L l Y"] by linarith
  qed
  hence "abs (\<rho> -  (real_of_int (C l w h g Y X))/(K k l w g Y X)) \<le> 1 - 1/8 - 1/2
    \<Longrightarrow> Y dvd (int (2*nat X choose nat X))"
    unfolding L_def using Y_dvd_iff by auto
  hence ineq_required: "abs (\<rho> - (real_of_int (C l w h g Y X))/(K k l w g Y X)) \<le> 1/4
    \<Longrightarrow> Y dvd (int (2*nat X choose nat X))" by auto

  have L_nonzero: "L l Y \<noteq> 0" unfolding L_def using lx_nonzero assms by auto
  hence "1+1/(2*abs (L l Y)) = (2*abs (L l Y))/(2*abs (L l Y)) + 1/(2*abs (L l Y))"
    using divide_self[of "2*abs (L l Y)"] by auto
  hence obv_eq_div2L: "1+1/(2*abs (L l Y)) = (2*abs (L l Y) + 1)/(2*abs (L l Y))"
    using add_divide_distrib[of "2*abs (L l Y)" 1 "2*abs (L l Y)"] by auto
  have polyploidisation: "1+1/(2*abs (L l Y)) > 0"
    by (smt (verit, ccfv_threshold) absL_Be1 of_int_pos zero_less_divide_1_iff)

  have absU_expr: "abs(U l X Y) = 2 * int(nat X) * abs (L l Y)" unfolding U_def using abs_mult XBe3
    by (metis (mono_tags) abs_ge_zero abs_numeral abs_of_nat int_nat_eq order_trans)
  hence aUBe2X:"2 * int (nat X) \<le> abs(U l X Y)" using absL_Be1 XBe3 by auto
  have VBe1: "V w g Y\<ge>1" using V_Be82is_power2X by (smt (verit) zero_less_power)
  have abs2X1: "nat (abs (2*X+1)) = 2*nat X+1" using XBe3 by simp
  have "C l w h g Y X = \<psi>_int (U l X Y*(V w g Y+1)) (2 * X + 1)" using C_is_\<psi>BA A_def B_def by metis
  hence C_\<psi>nat:"C l w h g Y X = \<psi> (U l X Y*(V w g Y+1)) (2 * nat X + 1)" using \<psi>_int_def abs2X1 XBe3
    using Groups.mult_ac(1) left_minus_one_mult_self one_add_one one_power2 power_0 power_add
      power_one_right by force
  have "K k l w g Y X = \<psi>_int (U l X Y^2*V w g Y) (X+1)" using K_is_\<psi>U2V by metis
  hence K_\<psi>nat: "K k l w g Y X = \<psi> (U l X Y^2*V w g Y) (nat X+1)" using \<psi>_int_def XBe3 nat2X12X
    by auto
  have "(C l w h g Y X) / (K k l w g Y X)
    = (\<psi> (U l X Y*(V w g Y+1)) (2 * nat X + 1)) / \<psi> (U l X Y^2*V w g Y) (nat X+1)"
    using C_\<psi>nat K_\<psi>nat by simp
  hence absCK\<rho>_expl:"abs (C l w h g Y X / K k l w g Y X - \<rho>)
    = abs ((\<psi> (U l X Y*(V w g Y+1)) (2 * nat X + 1)) / \<psi> (U l X Y^2*V w g Y) (nat X+1) - \<rho>)"
    by simp
  have "abs ((\<psi> (U l X Y*(V w g Y+1)) (2 * nat X + 1)) / \<psi> (U l X Y^2*V w g Y) (nat X+1) - \<rho>)
    \<le> (2 * int(nat X))* \<rho> / (abs(U l X Y) * V w g Y)"
    using XBe3 VBe1 aUBe2X \<rho>_def lemma_4_4_cor_rho_abs[of "nat X" "U l X Y" "V w g Y" \<rho>] by fastforce
  hence majCK\<rho>1: "abs ((C l w h g Y X) / (K k l w g Y X) - \<rho>) \<le> 2 * X * \<rho> / (abs(U l X Y) * V w g Y)"
    using absCK\<rho>_expl XBe3 by auto

  (* proof of \<rho> / |L|  < 4 *)

  have "abs(V w g Y + 1) = V w g Y + 1" using VBe1 by simp
  hence "abs (V w g Y + 1) - 1 / real_of_int (abs (U l X Y)) \<ge> V w g Y"
    using aUBe2X XBe3 by fastforce
  hence aV1invU_maj: "(real_of_int (abs(V w g Y + 1)) - 1 / real_of_int (abs (U l X Y)))^(2 * nat X)
    \<ge> (real_of_int (V w g Y))^(2 * nat X)"
    using XBe3 VBe1 by simp
  have "real_of_int (abs (U l X Y) ^ (2 * nat X)) \<ge> 0" using aUBe2X XBe3 by simp
  hence "real_of_int (abs (U l X Y) ^ (2 * nat X)) * (real_of_int (abs(V w g Y + 1))
    - 1 / real_of_int (abs (U l X Y)))^(2 * nat X)
    \<ge> real_of_int (abs(U l X Y) ^ (2 * nat X)) * (real_of_int (V w g Y))^(2 * nat X)"
    using aV1invU_maj mult_left_mono by fast
  hence other_ineq_\<psi>AB_3: "real_of_int (\<psi> (abs (A l w g Y X)) (2*nat X+1))
    \<ge> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((V w g Y)^(2*nat X))"
    using other_ineq_\<psi>AB by simp
  hence "\<psi> (abs (A l w g Y X)) (2*nat X+1) / \<psi> (abs (U l X Y^2*V w g Y)) (nat X+1)
    \<ge> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((V w g Y)^(2*nat X))
      / (real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int ((abs (V w g Y))^(nat X)))"
    using \<psi>AB_is_pos \<psi>U2V_is_pos other_ineq_\<psi>AB_3 frac_le ineq_\<psi>U2V by blast
  hence "abs (real_of_int (C l w h g Y X)/(K k l w g Y X))
    \<ge> real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int((V w g Y)^(2*nat X))
      / (real_of_int ((abs (U l X Y))^(2*nat X))*real_of_int ((abs (V w g Y))^(nat X)))"
    using eq2_CoverK by presburger
  hence "abs (real_of_int (C l w h g Y X)/(K k l w g Y X))
    \<ge> real_of_int((V w g Y)^(2*nat X)) / real_of_int ((abs (V w g Y))^(nat X))"
    using several_pow_pos by fastforce
  hence "abs (real_of_int (C l w h g Y X)/(K k l w g Y X))
    \<ge> real_of_int((V w g Y)^(2*nat X)) / real_of_int ((V w g Y)^(nat X))"
    using VBe1 by fastforce
  hence "abs (real_of_int (C l w h g Y X)/(K k l w g Y X))
    \<ge> real_of_int(V w g Y)^(2*nat X) / real_of_int (V w g Y)^(nat X)"
    by force
  hence aCoK_Be_VpoX: "abs (real_of_int (C l w h g Y X)/(K k l w g Y X))
    \<ge> real_of_int(V w g Y)^(nat X)"
    using VBe1 div_pow' by force
  hence "abs(L l Y) + 1/2 \<ge> (V w g Y)^(nat X)"
    using ineq3_CmLK by fastforce
  hence ineq_absL: "((V w g Y)^(nat X)/(abs (L l Y)+1/2)) \<le> 1"
    using polyploidisation divide_self[of "abs (L l Y)+1/2"]
      divide_right_mono[of "abs (L l Y) + 1/2" "(V w g Y)^(nat X)" "abs (L l Y)+1/2"] by simp
    
  have "abs(U l X Y) = 2 * X * abs(L l Y)" using absU_expr XBe3 by simp
  hence "2 * X * \<rho> / (abs(U l X Y) * V w g Y) = 2 * X * \<rho>  / (2 * X * abs(L l Y) * V w g Y)" by simp
  hence "2 * X * \<rho> / (abs(U l X Y) * V w g Y) = \<rho>  / (abs(L l Y) * V w g Y)"
    using of_int_mult[of "2 * X" "abs (L l Y) * V w g Y"] XBe3 Fields.field_class.mult_divide_mult_cancel_left
    by force
  hence rewrite_2X\<rho>: "2 * X * \<rho> / (abs(U l X Y) * V w g Y) = \<rho>  / (abs(L l Y)) * 1/(V w g Y)" by auto

  have simp_abs_L: "abs (L l Y)*(1+1/(2*abs (L l Y))) = abs (L l Y) + 1/2"
    using L_nonzero divide_self[of "abs (L l Y)"] distrib_left[of "abs (L l Y)" 1 "1/(2*abs (L l Y))"]
    by auto
  have "\<rho> / abs (L l Y) = (\<rho>/(V w g Y)^(nat X))*((V w g Y)^(nat X)
    /(abs (L l Y)*(1+1/(2*abs (L l Y)))))*(1+1/(2*abs (L l Y)))"
    using VBe8 polyploidisation by fastforce
  hence "\<rho> / abs (L l Y) = (\<rho>/(V w g Y)^(nat X))*((V w g Y)^(nat X)
    /(abs (L l Y)+1/2))*(1+1/(2*abs (L l Y)))"
    using simp_abs_L by metis
  hence rewrite_\<rho>L: "\<rho> / abs (L l Y)
    = (\<rho>/(V w g Y)^(nat X))*(1+1/(2*abs (L l Y)))*((V w g Y)^(nat X)/(abs (L l Y)+1/2))" by auto
  have \<rho>_pos: "\<rho> > 0" unfolding \<rho>_def using VBe1 by simp
  hence "(\<rho>/(V w g Y)^(nat X))*(1+1/(2*abs (L l Y))) \<ge> 0" using VBe8 polyploidisation by auto
  hence ineq_\<rho>L1: "\<rho> / abs (L l Y) \<le> (\<rho>/(V w g Y)^(nat X))*(1+1/(2*abs (L l Y)))"
    using ineq_absL rewrite_\<rho>L
      mult_left_mono[of "((V w g Y)^(nat X)/(abs (L l Y)+1/2))" 1 "(\<rho>/(V w g Y)^(nat X))*(1+1/(2*abs (L l Y)))"]
    by auto

  have "abs (L l Y) = abs l * Y" unfolding L_def using assms abs_mult[of l Y] by auto
  hence "abs (L l Y) \<ge> 2" using lx_nonzero assms mult_mono[of 1 "abs l" 2 Y] by auto
  hence "real_of_int (2*abs (L l Y)) \<ge> 4" by auto
  hence "1/(real_of_int (2*abs (L l Y))) \<le> 1/4"
    using inv_decr[of 4 "real_of_int (2*abs (L l Y))"] by auto
  hence "1 + 1/(real_of_int (2*abs (L l Y))) \<le> 5/4" by auto
  hence ineq_\<rho>L2: "\<rho> / abs (L l Y) \<le> (\<rho>/(V w g Y)^(nat X))*5/4"
    using mult_left_mono[of "1 + 1/(real_of_int (2*abs (L l Y)))" "5/4" "(\<rho>/(V w g Y)^(nat X))"]
      ineq_\<rho>L1 \<rho>_pos VBe8 by auto

  have bounding_1oV: "0 < 1/(V w g Y) \<and> 1/(V w g Y) \<le> 1" using VBe1 inv_decr[of 1 "V w g Y"] by auto
  have "\<rho>/(V w g Y)^(nat X) = (V w g Y +1)^(2*nat X)/((V w g Y)^(nat X)*(V w g Y)^(nat X))"
    unfolding \<rho>_def by auto
  hence "\<rho>/(V w g Y)^(nat X) = (V w g Y +1)^(2*nat X)/(V w g Y)^(nat X + nat X)"
    using power_add[of "V w g Y" "nat X" "nat X"] by auto
  hence "\<rho>/(V w g Y)^(nat X) = (real_of_int (V w g Y +1))^(2*nat X)/(real_of_int (V w g Y))^(2*nat X)"
    by (simp add: mult_2)
  hence "\<rho>/(V w g Y)^(nat X) = ((V w g Y +1)/(V w g Y))^(2*nat X)"
    using power_divide[of "real_of_int (V w g Y + 1)" "real_of_int (V w g Y)" "2*nat X"] by auto
  hence "\<rho>/(V w g Y)^(nat X) = ((V w g Y)/(V w g Y) +1/(V w g Y))^(2*nat X)"
    using VBe8 add_divide_distrib[of "V w g Y" 1 "V w g Y"] by auto
  hence "\<rho>/(V w g Y)^(nat X) = (1+1/(V w g Y))^(2*nat X)"
    using divide_self[of "V w g Y"] VBe8 by auto
  hence "\<rho>/(V w g Y)^(nat X) \<le> 1+(2^(2*nat X)-1)*(1/(V w g Y))"
    using bounding_1oV  power_majoration[of "1/(V w g Y)" "2*nat X"] by simp
  hence ineq_\<rho>V: "\<rho>/(V w g Y)^(nat X) \<le> 1+2^(2*nat X)/(V w g Y)"
    using bounding_1oV mult_right_mono[of "2^(2*nat X)-1" "2^(2*nat X)" "1/(V w g Y)"] by auto
  have "V w g Y \<ge> 2^(2*nat X)" using VBe1 V_Be82is_power2X by force
  hence "1/(V w g Y) \<le> 1/2^(2*nat X)" using inv_decr[of "2^(2*nat X)" "V w g Y"] by auto
  hence "2^(2*nat X)/(V w g Y) \<le> 1" using divide_self[of "2^(2*nat X)"]
    by (smt (z3) \<open>8 * 2 ^ (2 * nat X) \<le> real_of_int (V w g Y)\<close> bounding_1oV divide_nonneg_nonpos less_divide_eq_1_pos)
  hence "\<rho>/(V w g Y)^(nat X) \<le> 2" using ineq_\<rho>V by auto
  hence "\<rho> / abs (L l Y) < 4" using ineq_\<rho>L2 by auto

  (* Conclusion *)

  hence "2 * X * \<rho> / (abs(U l X Y) * V w g Y) \<le> 4*1/(V w g Y)"
    using VBe1 rewrite_2X\<rho> mult_right_mono[of "\<rho>/(abs (L l Y))" 4 "1/(V w g Y)"] by auto
  hence majCK\<rho>2: "abs ((C l w h g Y X) / (K k l w g Y X) - \<rho>) \<le> 4/V w g Y" using majCK\<rho>1 by auto
  have "V w g Y \<ge> 16" using V_Be82is_power2X XBe3 power_increasing[of 1 "2*nat X" 2]
    by (smt (verit, del_insts) \<open>2 * nat X = nat (2 * X)\<close> numeral_eq_one_iff numeral_power_le_nat_cancel_iff power_one_right)
  hence "4/(V w g Y) \<le> 1/4" using inv_decr[of 16 "V w g Y"] by auto
  hence "abs ((C l w h g Y X) / (K k l w g Y X) - \<rho>) \<le> 1/4" using majCK\<rho>2 by auto
  hence "abs (\<rho> - (C l w h g Y X) / (K k l w g Y X)) \<le> 1/4" by argo
  hence "Y dvd 2*nat X choose nat X" using ineq_required by simp

  then show "statement1 b Y X" unfolding statement1_def
    using \<open>2 * nat X = nat (2 * X)\<close> \<open>b\<ge>0\<close> is_power2_b by auto
qed

subsection \<open>Proof of implication \<open>(2a)\<Longrightarrow>(2)\<close>\<close>

lemma (in bridge_variables) theorem_II_3_2: (* 2a \<Longrightarrow> 2 *)
  assumes b_def:"(b::int)\<ge>0" and Y_def:"(Y::int)\<ge>b\<and>Y\<ge>2^8" and X_def:"(X::int)\<ge>3*b" and g_def:"(g::int)\<ge>1"
  shows "(statement2a b Y X g)\<Longrightarrow>(statement2 b Y X g)"
proof -
  assume "statement2a b Y X g"
  then obtain h k l w x y where stat3:"(d2a l w h x y g Y X)\<and>
          (d2b k l w x g Y X)\<and>(d2c l w h b g Y X)\<and>(d2e k l w h g Y X)
          \<and> (h\<ge>b)\<and>(k\<ge>b)\<and>(l\<ge>b)\<and>(w\<ge>b)\<and>(x\<ge>b)\<and>(y\<ge>b)" unfolding statement2a_def by auto
  then have d2a_b_c:"(d2a l w h x y g Y X)\<and>(d2b k l w x g Y X)\<and>(d2c l w h b g Y X)" by simp

  (* b>0 (copying the proof of 2 \<Longrightarrow> 1) *)
  have W_nonzero: "W w b \<noteq> 0"
  proof -
    have "W w b = 0 \<Longrightarrow> False"
    proof -
      assume hyp: "W w b = 0"
      hence "(2*A l w g Y X-5) dvd 2" using d2a_b_c unfolding d2c_def S_def T_def by auto
      hence "abs (2*A l w g Y X - 5) \<le> 2" using dvd_imp_le_int by presburger
      hence "2*A l w g Y X \<le> 7 \<and> 2*A l w g Y X \<ge> 3" by auto
      hence A_is_2_or_3: "A l w g Y X \<le> 3 \<and> A l w g Y X \<ge> 2" by auto
      have "abs (A l w g Y X) = abs (U l X Y) * abs (V w g Y + 1)"
        unfolding A_def U_def using abs_mult by auto
      hence eq: "abs (A l w g Y X) = 2*X*Y*abs l * abs (V w g Y +1)"
        unfolding U_def L_def using abs_mult[of "2*X" "l*Y"] abs_mult[of 2 X] abs_mult[of l Y] assms
        by auto
      hence X_nonzero: "X \<noteq> 0" using A_is_2_or_3 by auto
      have "l\<noteq>0" using A_is_2_or_3 unfolding A_def U_def L_def by force
      hence several_ineq: "X \<ge> 1 \<and> Y \<ge> 256 \<and> abs l \<ge> 1 \<and> abs (V w g Y +1) \<ge> 0"
        using assms X_nonzero by auto
      hence "2*X*Y \<ge> 2*256 \<and> abs l \<ge> 1 \<and> abs (V w g Y +1) \<ge> 0"
        using mult_mono[of 1 X 256 Y] mult_left_mono[of 256 "X*Y" 2] by force
      hence "(2*X*Y)*abs l*abs (V w g Y +1) \<ge> (2*256)*abs (V w g Y +1)"
        using mult_mono[of "2*256" "2*X*Y" 1 "abs l"]
          mult_right_mono[of "2*256" "2*X*Y*abs l" "abs (V w g Y +1)"] by linarith
      hence ineq: "2*X*Y*abs l * abs (V w g Y +1) \<ge> 2*256*abs (V w g Y +1)"
        by (auto simp add: mult_mono)
      hence "abs (A l w g Y X) \<ge> 2*256*abs (V w g Y +1)" using ineq eq by presburger
      hence "3 \<ge> 2*256*abs (V w g Y +1) \<and> abs (V w g Y +1) \<ge> 0" using A_is_2_or_3 by auto
      hence "abs (V w g Y +1) = 0"
        by (smt (verit, best) comm_semiring_class.distrib distrib_left distrib_right mult_cancel_left2
            mult_le_0_iff mult_mono ring_class.ring_distribs(1) ring_class.ring_distribs(2))
      hence "V w g Y +1 = 0" by auto
      hence "A l w g Y X = 0" unfolding A_def by auto
      then show "False" using A_is_2_or_3 by auto
    qed
    then show ?thesis by auto
  qed
  hence bB0: "b>0" unfolding W_def using assms by auto

  then have lxn0: "l*x \<noteq> 0" using stat3 by simp
  have 0: "(4 * g * C l w h g Y X - 4 * g * L l Y * K k l w g Y X)\<^sup>2 < (K k l w g Y X)\<^sup>2"
    using stat3 unfolding d2e_def bB0 by simp
  then have "(4 * g * C l w h g Y X - 4 * g * L l Y * K k l w g Y X)\<^sup>2
    = (2 * g)^2 *(2 * C l w h g Y X - 2 * L l Y * K k l w g Y X)\<^sup>2" by algebra
  then have 1: "(2 * g)^2 *(2 * C l w h g Y X - 2 * L l Y * K k l w g Y X)\<^sup>2 < (K k l w g Y X)\<^sup>2"
    using 0 by simp
  have "(2 * g)^2 \<ge> 1" using stat3 bB0 by (smt (z3) g_def one_le_power)
  then have "(2 * C l w h g Y X - 2 * L l Y * K k l w g Y X)\<^sup>2
    \<le> (2 * g)^2 * (2 * C l w h g Y X - 2 * L l Y * K k l w g Y X)\<^sup>2"
    using mult_right_mono by fastforce
  then have "(2 * C l w h g Y X - 2 * L l Y * K k l w g Y X)\<^sup>2 < (K k l w g Y X)\<^sup>2" using 1 by simp
  then have "d2f k l w h g Y X" unfolding d2f_def by simp
  then show ?thesis unfolding statement2_def using lxn0 d2a_b_c by fast
qed

end
