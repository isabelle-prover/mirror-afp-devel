theory DFI_square_0
  imports Pell_Equation
begin

subsection \<open>Square Criterion for Exponentiation\<close>

locale bridge_variables
begin
(* The _f means function *)
(* Arguments are always in alphabetical order*)
definition D_f:: "int \<Rightarrow> int \<Rightarrow> int" where
"D_f A C = (A^2 - 4) * C^2 + 4"

definition E_f::"int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"E_f C D x = C^2 * D * x"

definition F_f:: "int \<Rightarrow> int \<Rightarrow> int" where
"F_f A E = 4 * (A^2 - 4) * E^2 +1"

definition G_f:: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"G_f A C D E F = 1 + C * D * F - 2 * (A + 2) * (A-2)^2 * E^2"

definition H_f:: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"H_f B C F y = C + B * F + (2*y - 1) * C * F"

definition I_f:: "int \<Rightarrow> int \<Rightarrow> int" where
"I_f G H = (G^2 - 1) * H^2 + 1"

definition E_ACx:: " int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"E_ACx A C x = E_f C (D_f A C) x"

definition F_ACx:: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"F_ACx A C x = F_f A (E_ACx A C x)"

definition G_ACx:: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"G_ACx A C x = G_f A C (D_f A C) (E_ACx A C x) (F_ACx A C x)"

definition H_ABCxy:: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"H_ABCxy A B C x y = H_f B C (F_ACx A C x) y"

definition I_ABCxy:: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"I_ABCxy A B C x y = I_f (G_ACx A C x) (H_ABCxy A B C x y)"


lemma lemma_4_2_part_DF:
  fixes A B
  defines "C \<equiv> \<psi> A (nat B)"
  assumes evA: "even A" "A\<ge>4" "B\<ge>3"
  shows "\<forall>n. \<exists>x\<ge>n. is_square (D_f A C) \<and> is_square (F_ACx A C x)"
proof
  fix n (* n::int can be negative but this is not a problem *)

  (* The first assertion (D is square) is immediate *)
  have D_square: "is_square (D_f A C)" using C_def lucas_pell_part2[of "C" "A"]
    unfolding D_f_def is_square_def by auto

  (* Most of the work is required to establish the existence of the correct x *)
  define D where "D \<equiv> D_f A C"
  have C_pos: "C > 0" unfolding C_def using lucas_strict_monotonicity[of "A" "nat(B)-1"] assms by auto
  then have "(A^2 - 4) * C^2\<ge>0" using assms by auto
  then have D_pos: "D > 0" unfolding D_def D_f_def by auto
  have CD_pos: "4 * C^2 * D \<ge> 1" using C_pos D_pos
    by (metis add.left_neutral add_diff_cancel_right' linorder_not_less zero_less_mult_iff zero_less_numeral zero_less_power zle_diff1_eq)
  have "\<exists>q\<ge>2 + nat(n * (4 * C^2 * D)). \<psi> A q mod (4 * C^2 * D) = 0"
    using lucas_modN C_pos CD_pos int_one_le_iff_zero_less by blast
  then obtain q where prop_q: "q\<ge>2 + nat(n * (4 * C^2 * D)) \<and> \<psi> A q mod (4 * C^2 * D) = 0" by presburger
  then obtain x where prop_x: "\<psi> A q = x * (4 * C^2 * D)"
    by (metis zmod_eq_0_iff mult.commute)
  define E where "E = E_f C D x"
  define F where "F = F_f A E"
  then have "4 * F = (A\<^sup>2 - 4) * 4^2 * (C\<^sup>2 * D * x)\<^sup>2 + 4" unfolding F_f_def E_def E_f_def by auto
  also have "...  = (A\<^sup>2 - 4) * (4 * C\<^sup>2 * D * x)\<^sup>2 + 4" by (simp add: power_mult_distrib)
  finally have "4 * F = (A^2 - 4) * (\<psi> A q)^2 +4" using prop_x by (simp add: mult.commute)
  then have "is_square (4 * F)" using lucas_pell_part2[of "\<psi> A q" "A"] unfolding is_square_def by auto
  then obtain k where prop_k: "4 * F = k^2" unfolding is_square_def by auto
  then have "even (k^2)" by (metis dvd_mult2 even_numeral)
  then have "even k" by simp
  then obtain l where "k = 2 * l" by auto
  then have "F = l^2" using prop_k by simp
  then have F_square: "is_square F" unfolding is_square_def by auto
  (*  Tedious calculations to show x\<ge>n, partly because n::int, q::nat, x::int*)
  have "q \<ge> 2" using prop_q by auto
  then have "\<psi> A q \<ge> \<psi> 2 q" using lucas_monotone_A \<open>A\<ge>4\<close> by simp
  then have q_minor: "... \<ge> int(q)" using lucas_A_eq_2[of "q"] by simp
  then have "... \<ge> int(nat(n * (4 * C^2 * D)))" using prop_q by auto
  then have x_minor_1: "... \<ge> n * (4 * C^2 * D)" by linarith
  then have x_minor: "x \<ge> n" using prop_x
  proof (cases "n\<ge>0")
    case True
    then have "x * (4 * C^2 * D) \<ge> n * (4 * C^2 * D)" using x_minor_1 prop_x by auto
    then show ?thesis using CD_pos mult_right_le_imp_le by fastforce
  next
    case False
    have "\<psi> A q \<ge> 0" using q_minor by simp
    then have "x \<ge> 0" using prop_x C_pos D_pos
      by (metis mult_less_cancel_right not_less not_numeral_le_zero power2_eq_square times_int_code(2))
    then show ?thesis using \<open>\<not> n\<ge>0\<close> by simp
  qed
  
  have "F = F_ACx A C x" using F_def E_def D_def unfolding F_ACx_def E_ACx_def by simp
  then show "\<exists>x\<ge>n. is_square (D_f A C) \<and> is_square (F_ACx A C x)" using D_square F_square x_minor F_def E_def
    by auto
qed

definition y_num_ABCx :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"y_num_ABCx A B C x = \<psi> (2*(G_ACx A C x)) (nat B) - C + (C-B) * F_ACx A C x"

definition y_den_ABCx :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"y_den_ABCx A B C x = 2 * C * F_ACx A C x"

lemma lemma_4_2_y_grows:
  fixes A B
  defines "C \<equiv> \<psi> A (nat B)"
  defines "y_num \<equiv> y_num_ABCx A B C" and "y_den \<equiv> y_den_ABCx A B C" (* /!\ Currification *)
  assumes evA: "even A" "A\<ge>4" "B\<ge>3"
  shows "\<forall>m. \<exists>n. \<forall>x. x\<ge>n \<longrightarrow> y_num x \<ge> m * y_den x \<and> y_den x > 0"
proof
  have easy_part: "\<forall>x. y_den x > 0"
  proof
    fix x::int
    have A_min: "A^2-4 \<ge> 0" using assms by auto
    have C_min: "C > 0" unfolding C_def using lucas_monotone1[of A "nat B"] assms by auto
    show "y_den x > 0"
      unfolding y_den_def y_den_ABCx_def F_ACx_def F_f_def E_ACx_def E_f_def D_f_def
      using A_min C_min by fastforce
  qed

  fix m
  define n where n_def: "n = C + 1 + 16*abs m*C*(A^2-4)"
  have "\<forall>x. x\<ge>n \<longrightarrow> y_num x \<ge> m * y_den x \<and> y_den x > 0"
  proof safe
  fix x assume x_def: "x\<ge>n"
  define D where "D = D_f A C"
  define E where "E = E_ACx A C x"
  define F where "F = F_ACx A C x"
  define G where "G = G_ACx A C x"
  have C_pos: "C > 0" unfolding C_def using lucas_monotone1[of A "nat B"] assms by auto
  have A_min: "A^2-4 \<ge> 1" using \<open>A \<ge> 4\<close>
    by (smt (verit) one_less_numeral_iff power_one_right power_strict_increasing_iff semiring_norm(76))
  then have D_min: "D > 0" unfolding D_def D_f_def using C_pos
    by (smt (verit, ccfv_SIG) int_distrib(2) one_le_power zmult_zless_mono2)
  have n_min: "n > 0" using n_def C_pos assms A_min
    by (smt (verit, ccfv_SIG) int_distrib(3) int_distrib(4) zmult_zless_mono2)
  then have E_min0: "E \<ge> n"
    unfolding E_def E_ACx_def E_f_def using D_def D_min C_pos x_def
    by (smt (verit) dvdI mult.commute mult_pos_pos zdvd_imp_le zero_less_power)
  then have E_min1: "E > 0" using n_min by auto
  have n_min1: "n \<ge> C+1" unfolding n_def using A_min C_pos by auto
  have n_min2: "n \<ge> 16*abs m * C * (A^2-4)" unfolding n_def using C_pos by auto

  define g where "g = 2*(A^2-4)*(2*C*D-(A-2))"
  have C_min: "C \<ge> A" using lucas_monotone1[of A "nat B"] C_def assms by auto
  then have "2*C*D - (A-2) \<ge> 1" using D_min
    by (smt (verit) C_pos dvdI mult_pos_pos zdvd_imp_le)
  then have g_min: "g > 0" unfolding g_def using A_min by force
  have "G = 1 + C*D*(4*(A^2-4)*E^2+1) - 2*(A + 2)*(A - 2)^2*E^2"
    unfolding G_def G_ACx_def G_f_def F_ACx_def F_f_def D_def E_def by auto
  also have "... = 1 + C*D +  2*(A^2-4)*(2*C*D - (A-2))*E^2"
    by (auto simp add: algebra_simps power2_eq_square)
  also have "... = 1 + C*D + g*E^2" unfolding g_def by auto
  also have "... \<ge> g*E^2" using C_pos D_min by auto
  finally have G_min: "G \<ge> g*E^2".
  then have G_min2: "G \<ge> 1" using g_min E_min1
    by (smt (z3) mult_le_0_iff one_le_power)

  have triv1: "3 + (nat B - 3) = nat B" using assms by auto
  have C_min2: "C \<ge> B" using lucas_monotone3[of A "nat B"] C_def assms by auto
                                                                  
  have \<psi>_3: "\<psi> k 3 = k^2 - 1" for k
    by (simp add: numeral_3_eq_3 power2_eq_square)

  have fact1: "y_num x = \<psi> (2*G) (nat B) - C + (C-B)*F"
    unfolding y_num_def y_num_ABCx_def G_def F_def by auto
  also have fact2: "... \<ge> \<psi> (2*G) 3 - C + (C-B)*F"
    using lucas_monotone2[of "2*G" 3 "nat B - 3"] triv1 G_min2 by auto
  also have fact3: "\<psi> (2*G) 3 - C + (C-B)*F = (2*G)^2 -1 - C + (C-B)*F"
    using \<psi>_3[of "2*G"] by auto
  also have "... \<ge> 4*g^2*(E^2)^2 - 1 - C + (C-B)*F"
    using G_min apply (simp add: power2_eq_square algebra_simps)
    using E_min1 g_min G_min2
    by (smt (verit) mult.commute mult.left_commute mult_mono' mult_nonneg_nonneg)
  then have step1: "y_num x \<ge> 4*g^2*(E^2)^2 - 1 - C + (C-B)*F" using fact1 fact2 fact3 by auto 
  have fact4: "4*g^2*(E^2)^2 - 1 - C + (C-B)*F \<ge> 4*(E^2)^2 - 1 - C + (C-B)*F"
    using g_min apply simp
    by (meson E_min1 dvd_triv_right mult_pos_pos zdvd_imp_le zero_less_power)
  have "F > 0" unfolding F_def F_ACx_def F_f_def using assms by auto
  then have fact5: "4*(E^2)^2 - 1 - C + (C-B)*F \<ge> 4*(E^2)^2 - 1 - C" using C_min2 by auto
  have "(E^2)^2 \<ge> E^2" using power2_eq_square[of "E^2"]
    by (smt (z3) one_le_numeral power2_less_eq_zero_iff power_increasing power_one_right)
  then have "(E^2)^2 \<ge> E" using power2_eq_square E_min1
    by (smt (verit, ccfv_SIG) power2_le_imp_le zero_le_power2)
  then have "(E^2)^2 \<ge> n" using E_min0 by auto
  then have "(E^2)^2 \<ge> C+1" using n_min1 by auto
  then have "4*(E^2)^2 - 1 - C \<ge> 3*(E^2)^2" by auto
  then have step2: "y_num x \<ge> 3*(E^2)^2" using step1 fact4 fact5 by auto

  have fact6: "4*(A^2-4)*E^2 \<ge> 1" using A_min E_min1
    by (smt (verit) mult_pos_pos power2_less_eq_zero_iff)
  have triv2: "k > 0 \<Longrightarrow> k \<le> l \<Longrightarrow> abs m * k \<le> abs m * l" for k l::int
    by (simp add: mult.commute mult_le_cancel_right)
  have fact7: "m * y_den x \<le> abs m * y_den x" using easy_part by auto
  have "y_den x = 2*C*(4*(A^2-4)*E^2 + 1)" unfolding y_den_def y_den_ABCx_def F_ACx_def F_f_def E_def by simp
  then have "y_den x \<le> 2*C*(4*(A^2-4)*E^2 + 4*(A^2-4)*E^2)"
    using C_pos fact6 by (smt (verit, ccfv_SIG) zmult_zless_mono2)
  then have step3: "y_den x \<le> 16 * C * (A^2-4) * E^2"
    by (auto simp add: algebra_simps)
  then have "abs m * y_den x \<le> abs m * (16 * C * (A^2 - 4) * E^2)"
    using easy_part triv2[of "y_den x" "(16 * C * (A^2 - 4) * E^2)"] by auto
  then have "abs m * y_den x \<le> (16 * abs m * C * (A^2-4)) * E^2" by auto
  then have "abs m * y_den x \<le> n*E^2" using n_min2 E_min1
    by (smt (verit, ccfv_SIG) mult_right_less_imp_less not_sum_power2_lt_zero)
  then have "m * y_den x \<le> n * E^2" using fact7 by auto
  then have "m*y_den x \<le> E* E^2" using E_min0 E_min1
    by (smt (verit) mult_right_less_imp_less zero_le_power)
  then have "m*y_den x \<le>3*(E^2)^2" using E_min1 power2_eq_square[of "E^2"]
    by (smt (verit) \<open>E\<^sup>2 \<le> (E\<^sup>2)\<^sup>2\<close> mult_right_mono power_eq_0_iff power_strict_mono zero_power2)
  then have "m*y_den x \<le> y_num x" using step2 by auto
  then show "y_num x \<ge> m*y_den x" using easy_part by auto
next
  show "\<And>x. n \<le> x \<Longrightarrow> 0 < y_den x" using easy_part by auto
qed
  then show "\<exists>n. \<forall>x\<ge>n. m * y_den x \<le> y_num x \<and> 0 < y_den x" by auto
qed

(* Helper lemma *)

lemma mod_mult:
  fixes a::int and b::int and c::int and d::int
  assumes "a mod c = b mod c \<and> a mod d = b mod d \<and> coprime c d"
  shows "a mod (c*d) = b mod (c*d)"
proof -
  have "c dvd (b-a) \<and> d dvd (b-a)" using assms by (metis mod_eq_dvd_iff)
  then have "(c*d) dvd (b-a)" using assms by (simp add: divides_mult)
  then show ?thesis using mod_eq_dvd_iff by metis
qed


lemma lemma_4_2_y_int:
  fixes A B x
  defines "C \<equiv> \<psi> A (nat B)"
  defines "y_num \<equiv> y_num_ABCx A B C" and "y_den \<equiv> y_den_ABCx A B C" (* /!\ Currification *)
  assumes evA: "even A" "A\<ge>4" "B\<ge>3"
  shows "y_den x dvd y_num x"
proof -
  define D where "D \<equiv> D_f A C"
  define E where "E = E_f C D x"
  define F where "F = F_f A E"
  define G where "G = G_f A C D E F"
  define H0 where "H0 = \<psi> (2*G) (nat B)"

  have minG: "G \<ge> 1+A"
  proof -
    have min_A: "A^2-4\<ge> 0" using assms by auto
    then have minD: "D \<ge> 1" using D_def D_f_def by simp
    have minF: "F \<ge> 1" using F_def F_f_def min_A by auto
    have a1: "G = 1 + C*D*F - 2*(A+2)*(A-2)^2*E^2" using G_def G_f_def by auto
    have a2: "... \<ge> 1 + A*D*F - 2*(A+2)*(A-2)^2*E^2"
      using assms lucas_monotone1[of A "nat B"] minD minF by auto
    have a3: "1 + A*D*F - 2*(A+2)*(A-2)^2*E^2 \<ge> 1 + A*F - 2*(A+2)*(A-2)^2*E^2"
      using minD minF evA(2) by fastforce
    have a4: "1 + A*F - 2*(A+2)*(A-2)^2*E^2 = 1 + A*(4*(A^2-4)*E^2+1) - 2*(A+2)*(A-2)^2*E^2"
      using F_def F_f_def[of A E] by auto
    have a5: "1 + A*(4*(A^2-4)*E^2+1) - 2*(A+2)*(A-2)^2*E^2 = 1 + A + 4*A*(A^2-4)*E^2 - 2*(A+2)*(A-2)^2*E^2"
      by (auto simp add: algebra_simps)
    have a6: "1+A + 4*A*(A^2-4)*E^2 - 2*(A+2)*(A-2)^2*E^2 \<ge> 1+A + 2*A*(A^2-4)*E^2 - 2*(A+2)*(A-2)^2*E^2"
      using assms min_A by auto
    have a7: "1+A + 2*A*(A^2-4)*E^2 - 2*(A+2)*(A-2)^2*E^2 \<ge> 1+A + 2*(A-2)*(A^2-4)*E^2 - 2*(A+2)*(A-2)^2*E^2"
      using min_A by (smt (z3) mult_right_mono zero_le_power2)
    have a8: "1+A + 2*(A-2)*(A^2-4)*E^2 - 2*(A+2)*(A-2)^2*E^2 = 1+A"
      by (auto simp add: algebra_simps power2_eq_square)
    show ?thesis
      using a1 a2 a3 a4 a5 a6 a7 a8 by linarith
  qed

  have "H0 mod (2*G-2)= \<psi> (2*G) (nat B) mod (2*G-2)" using H0_def by simp
  also have "... = B mod (2*G-2)" using lucas_congruence2[of "2*G" "nat B"] assms minG
    dvd_refl even_nat_iff even_numeral by auto
  finally have H0_1: "H0 mod (2*G-2) = B mod (2*G-2)".

  have "H0 mod (2*G-A) = \<psi> (2*G) (nat B) mod (2*G-A)" using H0_def by simp
  also have "... = C mod (2*G-A)" using C_def lucas_congruence[of "2*G-A" "2*G" "A" "nat B"] minG
    by (smt (z3) evA(2) mod_add_self2)
  finally have H0_2: "H0 mod (2*G-A) = C mod (2*G-A)".

  have "2*G-A = 2*(1 + C*D*F - 2*(A+2)*(A-2)^2*E^2)-A" using G_def G_f_def by auto
  also have "... = 2*(1+D*C*F) - 4*(A^2-4)*E^2*(A-2) - A"
    by (auto simp add: algebra_simps power2_eq_square)
  also have "... = 2*(1+D*C*F) - (F-1)*(A-2) - A"
  proof -
    have "F-1 = 4*(A^2-4)*E^2" using F_def F_f_def by auto
    then show ?thesis by auto
  qed
  also have "... = F*(2*D*C - A + 2)"
    by (auto simp add: algebra_simps)
  finally have G_moins: "2*G-A = F*(2*D*C - A + 2)".

  have "H0 mod F = C mod F"
    using G_moins H0_2 by (metis dvd_triv_left mod_mod_cancel)
  also have "... = (C + B*F - C*F) mod F"
    by (smt (verit) mod_mult_self3)
  finally have H0_3: "H0 mod F = (C + B*F - C*F) mod F".

  have C_div_E: "C dvd E" using E_def E_f_def by simp
  then have C_div_E: "2*C dvd 2*E" by auto
  have "(2*G-2) mod (2*C) = 2*(C*D*F - 2*(A+2)*(A-2)^2*E^2) mod (2*C)"
    using G_def G_f_def[of A C D E F] by auto
  also have "... = (2*C*(D*F)+(-(A+2)*(A-2)^2*(2*E)*2*E)) mod (2*C)"
    by (auto simp add: algebra_simps power2_eq_square)
  also have "... =-(A+2)*(A-2)^2*(2*E)*2*E  mod (2*C)"
    using mod_mult_self4[of "2*C" "D*F"  "-(A+2)*(A-2)^2*(2*E)*2*E"]  by auto
  also have "... = 0 mod (2*C)" using C_div_E by fastforce
  finally have "(2*G-2) mod (2*C) = 0 mod (2*C)".
  then have C_and_G: "2*C dvd (2*G-2)" by auto

  have evCB: "even (C-B)" using lucas_parity2[of A "nat B"] C_def assms by auto
  have C_div_F: "2*C dvd (F-1)"
  proof -
    have "F-1 = 4* (A^2-4)*E*E" unfolding F_def F_f_def using power2_eq_square[of E] by simp
    then show ?thesis using C_div_E by auto
  qed
  have "H0 mod (2*C) = B mod (2*C)"
    using C_and_G H0_1 by (metis mod_mod_cancel)
  also have "... = (B + (B-C)*(F-1)) mod (2*C)"
    using C_div_F by (metis dvdE dvd_mult mod_mult_self2)
  also have "... = (C + B*F - C*F) mod (2*C)"
    by (auto simp add: algebra_simps)
  finally have H0_4: "H0 mod (2*C) = (C + B*F - C*F) mod (2*C)".

  have "coprime F (2*C)"
  proof -
    obtain k where k_def: "F-1 = k*2*C" using C_div_F by (metis dvdE mult.assoc mult.commute)
    have "1 = F - (2*C)*k" using k_def by (auto simp add: algebra_simps)
    then show ?thesis by (meson C_div_F coprime_def coprime_doff_one_right dvd_trans)
  qed

  then have "H0 mod (2*C*F) = (C + B*F - C*F) mod (2*C*F)"
    using H0_4 H0_3 mod_mult[of H0 F "C + B*F - C*F" "2*C"] by (auto simp add: algebra_simps)
  then have H0_5: "2*C*F dvd (H0 - (C + B*F - C*F))" using mod_eq_dvd_iff by blast

  have y_den_ok: "y_den x = 2*C*F"
    unfolding y_den_def y_den_ABCx_def F_ACx_def E_ACx_def F_def E_def D_def by simp
  have y_num_ok: "y_num x = H0 - (C + B*F - C*F)"
    unfolding y_num_def y_num_ABCx_def G_ACx_def E_ACx_def F_ACx_def H0_def G_def D_def E_def F_def
    by (simp add: algebra_simps)
  then show ?thesis using y_den_ok H0_5 by simp
qed


(* Take m=n in preceding lemma, and n = max(this m, the n given by the lemma) *)

lemma lemma_4_2:
  fixes A B n
  defines "C \<equiv> \<psi> A (nat B)"
  assumes evA: "even A" "A\<ge>4" "B\<ge>3"
  shows "\<exists>x\<ge>n. \<exists>y\<ge>n. is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y)"
proof -
  define y_num y_den where "y_num \<equiv> y_num_ABCx A B C" and "y_den \<equiv> y_den_ABCx A B C"
  obtain m where y_prop: "\<forall>x. x\<ge>m \<longrightarrow> y_num x \<ge> n * y_den x \<and> y_den x > 0"
    unfolding y_num_def y_den_def using assms lemma_4_2_y_grows[of A B] by auto
  obtain x where  x_big_DF_square: "x \<ge> abs m+abs n \<and> is_square (D_f A C) \<and> is_square (F_ACx A C x)"
    using assms lemma_4_2_part_DF[of A B] by auto
  obtain y where y_def: "y_num x = y_den x * y"
    unfolding y_num_def y_den_def using lemma_4_2_y_int[of A B x] assms by auto
  have x_big': "x \<ge> m" using x_big_DF_square by linarith
  then have y_big: "y \<ge> n" using y_prop y_def by auto
  have x_big: "x \<ge> n" using x_big_DF_square by linarith
  define F where "F = F_ACx A C x"
  define G where "G = G_ACx A C x"
  define H where "H = H_ABCxy A B C x y"
  define I where "I = I_ABCxy A B C x y"
  have "H*y_den x = (C + B*F + (2*y-1)*C*F)*y_den x"
    unfolding H_def H_ABCxy_def H_f_def F_def by simp
  also have "... = (C + B*F - C*F)*y_den x + 2*C*F*y_num x"
    using y_def by (auto simp add: algebra_simps)
  also have "... = (C + B*F - C*F)*2*C*F + 2*C*F*(\<psi> (2 * G) (nat B) - C + (C - B) * F)"
    unfolding y_den_def y_den_ABCx_def y_num_def y_num_ABCx_def F_def G_def by auto
  also have "... = 2*C*F*\<psi> (2*G) (nat B)"
    by (simp add: algebra_simps)
  also have "... = y_den x * \<psi> (2*G) (nat B)"
    unfolding y_den_def y_den_ABCx_def F_def by simp
  finally have "H = \<psi> (2*G) (nat B)" using y_prop x_big' by auto
  then have "\<exists>m. H =  \<psi> (2 * G) m \<or> H =  - \<psi> (2 * G) m" by auto
  then have "is_square I"
    unfolding I_def I_ABCxy_def I_f_def H_def G_def
    using lucas_pell_corollary[of "G_ACx A C x" "H_ABCxy A B C x y"] by auto
  then have "x \<ge> n \<and> y \<ge> n \<and> is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y)"
    unfolding I_def using x_big_DF_square y_big x_big by auto
  then show ?thesis by auto
qed

lemma lemma_4_2_cor:
  fixes A B
  defines "C \<equiv> \<psi> A (nat B)"
  assumes evA: "even A" "A\<ge>4" "B\<ge>3"
  shows "\<forall>n. \<exists>x\<ge>n. \<exists>y\<ge>n. is_square ((D_f A C) * (F_ACx A C x) * (I_ABCxy A B C x y))"
proof
  fix n
  obtain x y where prop_36: "x\<ge>n \<and> y\<ge>n \<and> is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y)"
    using lemma_4_2[of A B n] assms by auto
  obtain d f i where "d^2 = D_f A C \<and> f^2 = F_ACx A C x \<and> i^2 = I_ABCxy A B C x y"
    using prop_36 is_square_def by metis
  then have "(d*f*i)^2 = (D_f A C) * (F_ACx A C x) * (I_ABCxy A B C x y)"
    by (auto simp add: power2_eq_square algebra_simps)
  then have "is_square ((D_f A C) * (F_ACx A C x) * (I_ABCxy A B C x y))" unfolding is_square_def by metis
  then show "\<exists>x\<ge>n. \<exists>y\<ge>n. is_square ((D_f A C) * (F_ACx A C x) * (I_ABCxy A B C x y))"
    using prop_36 by auto
qed

end

end
