theory DFI_square_3
  imports DFI_square_2
begin

text \<open>A few lemmas before the proof\<close>

lemma lucas_pell_corollary_int:
  fixes A::int and X::int
  shows "(\<exists>k. (A^2-4)*X^2 + 4 = k^2) \<Longrightarrow>(\<exists>m. X = \<psi>_int A m)"
proof -
  assume assumption: "(\<exists>k. (A^2-4)*X^2 + 4 = k^2)"
  then obtain m0 where m0_def: "X = \<psi> A m0 \<or> X = -\<psi> A m0" using lucas_pell_part1 by auto
  then obtain e where e_def: "X = e*\<psi> A m0 \<and> (e=1 \<or> e=-1)" by force
  define m where "m \<equiv> e* int m0"
  hence m_def: "X = \<psi>_int A m"
    using \<psi>_int_def[of A m] m0_def e_def mult_minus_left power_one_right by fastforce
  then show ?thesis by auto
qed

lemma lucas_modN_int:
  fixes A::int and B::int and n::int
  assumes "A mod n = B mod n"
  shows "(\<psi>_int A m) mod n = (\<psi>_int B m) mod n"
proof (cases m)
  case (nonneg k)
  then show ?thesis
    using lucas_congruence[of n A B k] \<psi>_int_def[of A m] \<psi>_int_def[of A m] \<psi>_int_def[of B m] assms
    by auto
next
  case (neg k)
  then show ?thesis
    using lucas_congruence[of n A B "Suc k"] \<psi>_int_def[of A m] \<psi>_int_def[of A m] \<psi>_int_def[of B m] assms
    apply simp by (metis Suc_as_int mod_minus_eq)
qed

lemma div_mod: "(n::int) dvd m \<Longrightarrow> k mod m = l mod m \<Longrightarrow> k mod n = l mod n"
proof -
  assume assm1: "n dvd m"
  assume assm2: "k mod m = l mod m"
  hence "(k-l) mod m = 0 mod m" using mod_diff_cong[of k m l l l] by auto
  hence "m dvd (k-l)" by auto
  hence "n dvd (k-l)" using assm1 by auto
  hence "(k-l) mod n = 0 mod n" by auto
  thus ?thesis using mod_add_cong[of "k-l" n 0 l l] by auto
qed

lemma \<psi>_int_minusA: "\<psi>_int (-X) n = (-1)^(nat (abs n) +1)*\<psi>_int X n" for n X
proof (cases n)
  case (nonneg k)
  note t=this
  hence "k=nat (abs n)" by auto
  then show ?thesis using lucas_symmetry_A2[of "-X" k] \<psi>_int_def[of "-X" n] \<psi>_int_def[of X n] t by auto
next
  case (neg k)
  note t=this
  hence "Suc k = nat (abs n)" by auto
  then show ?thesis using lucas_symmetry_A2[of "-X" "Suc k"] \<psi>_int_def[of "-X" n] \<psi>_int_def[of X n] t
    apply simp by (smt (z3) mult.assoc mult.commute)
qed


lemma eq_\<psi>_int: "abs X > 1 \<Longrightarrow> abs (\<psi>_int X n) = \<psi> (abs X) (nat (abs n))" for X n
  proof -
    assume assm: "abs X > 1"
    then show ?thesis
    proof (cases X)
      case (nonneg Y)
      hence "abs (\<psi>_int X n) = abs (\<psi>_int (abs X) n)" by auto
      hence "abs (\<psi>_int X n) = abs ((-1)^(if 0 \<le> n then 0 else 1) * \<psi> (abs X) (nat (abs n)))"
        using \<psi>_int_def[of "abs X" n] by auto
      hence "abs (\<psi>_int X n) = abs ((-1)^(if 0 \<le> n then 0 else 1))*abs (\<psi> (abs X) (nat (abs n)))"
        using abs_mult by auto
      hence "abs (\<psi>_int X n) = abs (\<psi> (abs X) (nat (abs n)))" by auto
      then show ?thesis using lucas_monotone3[of "abs X" "nat (abs n)"] assm by auto
    next
      case (neg Y)
      hence "-X = abs X" by auto
      hence "abs (\<psi>_int X n) = abs ((-1)^(nat (abs n)+1)*\<psi>_int (abs X) n)"
        using \<psi>_int_minusA[of "-X" n] by (smt (verit))
      hence "abs (\<psi>_int X n) = abs ((-1)^(nat (abs n)+1))*abs (\<psi>_int (abs X) n)"
        using abs_mult by metis
      hence "abs (\<psi>_int X n) = abs (\<psi>_int (abs X) n)" by auto
      hence "abs (\<psi>_int X n) = abs ((-1)^(if 0 \<le> n then 0 else 1) * \<psi> (abs X) (nat (abs n)))"
        using \<psi>_int_def[of "abs X" n] by auto
      hence "abs (\<psi>_int X n) = abs ((-1)^(if 0 \<le> n then 0 else 1))*abs (\<psi> (abs X) (nat (abs n)))"
        using abs_mult by auto
      hence "abs (\<psi>_int X n) = abs (\<psi> (abs X) (nat (abs n)))" by auto
      then show ?thesis using lucas_monotone3[of "abs X" "nat (abs n)"] assm by auto
    qed
  qed

text \<open>Lemma 10 in Sun\<close>

lemma sun_lemma10_dir_int:
  fixes A::int and n::int and s::int and t::int and k::int
  assumes "abs A > 2" and "n > 3" and "\<chi>_int (abs A) n = 2*k"
  shows "(\<psi>_int A s mod k = \<psi>_int A t mod k)
      \<Longrightarrow> (s mod (2*n) = t mod (2*n) \<or> (s+t) mod (2*n) = 0 mod (2*n))"
proof -
  assume hyp: "(\<psi>_int A s mod k = \<psi>_int A t mod k)"
  then show ?thesis
  proof (cases A)
    case (nonneg B)
    then show ?thesis using sun_lemma10_dir[of B n k s t] assms hyp div_mod[of "2*n" "4*n" s t]
        div_mod[of "2*n" "4*n" "s+t" "2*n"] gr0I mod_eq_0_iff_dvd
        mod_self of_nat_0_less_iff zmod_int by auto
  next
    case (neg B)
    note t = this
    define C where "C = abs A"
    hence C_def2: "C = -A" using t by auto
    have "(-1)^(nat (abs s) +1)*\<psi>_int C s mod k = (-1)^(nat (abs t)+1)*\<psi>_int C t mod k"
      using hyp \<psi>_int_minusA[of "-A" s] \<psi>_int_minusA[of "-A" t] C_def2 by auto
    hence eq: "(-1)^(nat (abs s)+1)*\<psi>_int C s*(-1)^(nat (abs s)+1) mod k
      = (-1)^(nat (abs t)+1)*\<psi>_int C t*(-1)^(nat (abs s)+1) mod k"
      using mod_mult_cong[of "(-1)^(nat (abs s) +1)*\<psi>_int C s" k "(-1)^(nat (abs t) +1)*\<psi>_int C t"
          "(-1)^(nat (abs s)+1)" "(-1)^(nat (abs s)+1)"] by blast
    hence "\<psi>_int C s mod k = \<psi>_int C t mod k \<or> \<psi>_int C s mod k = (-\<psi>_int C t) mod k"
      by (smt (z3) left_minus_one_mult_self minus_one_mult_self mod_minus_minus mult.left_commute
          mult_cancel_left2 mult_minus_right square_eq_1_iff)
    hence "\<psi>_int C s mod k = \<psi>_int C t mod k \<or> \<psi>_int C s mod k = \<psi>_int C (-t) mod k"
      using \<psi>_int_odd[of C t] by auto
    hence "s mod (4*n) = t mod (4*n) \<or> (s+t) mod (4*n) = 2*n mod (4*n)
        \<or> s mod (4*n) = (-t) mod (4*n) \<or> (s-t) mod (4*n) = 2*n mod (4*n)"
      using sun_lemma10_dir[of C n k s t] sun_lemma10_dir[of C n k s "-t"] hyp assms
      by (metis C_def add.inverse_inverse diff_minus_eq_add)
    hence "s mod (2*n) = t mod (2*n) \<or> (s+t) mod (2*n) = 0 mod (2*n)
        \<or> s mod (2*n) = (-t) mod (2*n) \<or> (s-t) mod (2*n) = 0 mod (2*n)" 
      using div_mod[of "2*n" "4*n" s t] div_mod[of "2*n" "4*n" "s+t" "2*n"]
        div_mod[of "2*n" "4*n" s "-t"] div_mod[of "2*n" "4*n" "s-t" "2*n"] by auto
    then show ?thesis using mod_add_cong[of s "2*n" "-t" t t] mod_add_cong[of "s-t" "2*n" 0 t t]
      by auto
  qed
qed

text \<open>Theorem in Sun\<close>

theorem (in bridge_variables) sun_theorem:
  fixes A::int and B::int and C::int and x::int and y::int
  assumes "abs B > 1" and "2*abs B < abs A - 2" and "(A-2) dvd (C-B)" and "x \<noteq> 0"
and "is_square (D_f A C * F_ACx A C x * I_ABCxy A B C x y)"
shows "C = \<psi>_int A B"
proof -
  have A_B2: "abs A > 2" using assms by auto
  have "A^2 = (abs A)^2" by auto
  hence A_pos: "A^2-4 > 0"
    using assms power2_eq_square[of "abs A"] mult_strict_mono[of 2 "abs A" 2 "abs A"] by auto
  have DFI_sq: "(is_square (D_f A C) \<and> is_square (F_ACx A C x) \<and> is_square (I_ABCxy A B C x y))"
    using sun_lemma24[of A C x B y] assms by auto
  then obtain s where s_def: "C = \<psi>_int A s"
    using lucas_pell_corollary_int[of A C] D_f_def[of A C] is_square_def[of "D_f A C"] by auto
  obtain k0 where k_def: "k0^2 = F_ACx A C x" using DFI_sq is_square_def by metis
  hence "(2*k0)^2 = (A^2-4)*(4*E_ACx A C x)^2 + 4"
    unfolding F_ACx_def F_f_def by (auto simp add: algebra_simps)
  then obtain m where m_def: "4*E_ACx A C x = \<psi>_int A m"
    using lucas_pell_corollary_int[of A "4*E_ACx A C x"] by metis
  obtain k1 where k1_def: "k1^2 = I_ABCxy A B C x y" using DFI_sq is_square_def by metis
  hence "(2*k1)^2 = ((2*G_ACx A C x)^2-4)*H_ABCxy A B C x y^2+4"
    unfolding I_ABCxy_def I_f_def using power_mult_distrib[of 2 k1 2] by (auto simp add: algebra_simps)
  then obtain t where t_def: "H_ABCxy A B C x y = \<psi>_int (2*G_ACx A C x) t"
    using lucas_pell_corollary_int[of "2*G_ACx A C x" "H_ABCxy A B C x y"] by metis 

  have sB1: "abs s > 1"
  proof -
    consider (0) "s=0" | (1) "s=1" | (m1) "s=-1" | (ok) "abs s > 1" by linarith
    then show ?thesis
    proof (cases)
      case 0
      hence "C= 0" using s_def \<psi>_int_def[of A s] by auto
      hence "(A-2) dvd B" using assms by auto
      hence "abs B \<ge> abs (A-2)" using assms using dvd_imp_le_int by force
      hence "abs B \<ge> abs A - 2" by auto
      hence "abs A - 2 > 2*abs A - 4" using assms by auto
      then show ?thesis using assms by auto
    next
      case 1
      hence "C= 1" using s_def \<psi>_int_def[of A s] by auto
      hence "(A-2) dvd (B-1)" using assms by presburger
      hence "abs (B-1) \<ge> abs (A-2)" using assms using dvd_imp_le_int by fastforce
      hence "abs B + 1 \<ge> abs A - 2" by auto
      hence "abs A > 2*abs A - 4" using assms by auto
      then show ?thesis using assms by auto
    next
      case m1
      hence "C= -1" using s_def \<psi>_int_def[of A s] by auto
      hence "(A-2) dvd (-1-B)" using assms by presburger
      hence "abs (-1-B) \<ge> abs (A-2)" using assms using dvd_imp_le_int by fastforce
      hence "abs B + 1 \<ge> abs A - 2" by auto
      hence "abs A > 2*abs A - 4" using assms by auto
      then show ?thesis using assms by auto
    qed
  qed

  hence C_Bigger_A: "abs C \<ge> abs A"
  proof -
    have "abs C = abs (\<psi>_int A s)" using s_def by auto
    hence "abs C = \<psi> (abs A) (nat (abs s))" using eq_\<psi>_int[of A s] A_B2 by auto
    hence "abs C \<ge> \<psi> (abs A) (Suc (Suc 0))"
      using sB1 lucas_monotone4[of "abs A" "Suc (Suc 0)" "nat (abs s)"] A_B2 by auto
    then show ?thesis by auto
  qed

  hence C_Bigger_B: "abs C > abs B" using assms by auto
  hence C_nonzero: "C \<noteq> 0" by auto
  hence C2Be1: "C^2 \<ge> 1" by (smt (verit, best) power2_less_eq_zero_iff)
  have DBe4: "D_f A C \<ge> 4" unfolding D_f_def using A_pos by force
  have DBeA2: "D_f A C \<ge> A^2" unfolding D_f_def using A_pos mult_left_mono[of 1 "C^2" "A^2-4"] C2Be1
    by presburger
  have E_non0: "E_ACx A C x \<noteq> 0" unfolding E_ACx_def E_f_def using DBe4 assms C_nonzero by auto
  define n where "n = nat (abs m)"
  hence \<psi>_A_n_eq_4E: "\<psi> (abs A) n = abs (4*E_ACx A C x)" using m_def eq_\<psi>_int[of A m] assms by auto
  hence eq_\<psi>n: "\<psi> (abs A) n = 4*C^2*D_f A C * abs x" unfolding E_ACx_def E_f_def using C2Be1 DBe4
    by (auto simp add: abs_mult)
  hence "\<psi> (abs A) n \<ge> D_f A C" using C2Be1 assms DBe4 apply simp by (smt (z3) mult_le_0_iff)
  hence "\<psi> (abs A) n > A*A - 1" using DBeA2 power2_eq_square[of A] by auto
  hence "\<psi> (abs A) n > \<psi> A (Suc (Suc (Suc 0)))" by auto
  hence "n > Suc (Suc (Suc 0))" using lucas_monotone4[of "abs A" n "Suc (Suc (Suc 0))"] assms
    apply simp using le_eq_less_or_eq nat_le_linear by blast
  hence nB3: "3 < int n" by auto
  have "\<chi> (abs A) n^2 mod 4 = ((A^2-4)*\<psi> (abs A) n^2 + 4) mod 4"
    using lucas_pell_part3[of "abs A" n] by auto
  hence "\<chi> (abs A) n^2 mod 4 = (A^2-4)*(C^2*D_f A C*abs x*4)^2 mod 4"
    using eq_\<psi>n by (auto simp add: algebra_simps)
  hence "\<chi> (abs A) n^2 mod 4 = (A^2-4)*(C^2*D_f A C*abs x)^2*4*4 mod 4"
    using power_mult_distrib[of "C^2*D_f A C*abs x" 4 2] power2_eq_square[of 4] by auto
  hence "\<chi> (abs A) n^2 mod 4 = 0 mod 4" by simp
  hence "4 dvd \<chi> (abs A) n^2" by presburger
  hence "2^2 dvd \<chi> (abs A) n^2" by auto
  hence even_\<chi>: "2 dvd \<chi> (abs A) n"
    by (smt (z3) bits_one_mod_two_eq_one even_push_bit_iff exp_dvdE mod2_eq_if one_power2 power_mod
        zero_neq_numeral)
  then obtain k where k_def: "\<chi> (abs A) n = 2*k" by auto
  hence k_def2: "\<chi>_int (abs A) (int n) = 2*k" using \<chi>_int_def[of "abs A" "int n"] by auto

  have FBe1: "F_ACx A C x \<ge> 1"
    unfolding F_ACx_def F_f_def using A_pos mult_mono[of 0 "A^2-4" 0 "E_ACx A C x^2"] by auto
  have H_eqC_modF: "H_ABCxy A B C x y mod (F_ACx A C x) = C mod (F_ACx A C x)"
    unfolding H_ABCxy_def H_f_def by auto
  have "2*G_ACx A C x mod (F_ACx A C x) =
      (2*C*D_f A C * F_ACx A C x + (2-4*(A+2)*(A-2)^2*E_ACx A C x^2)) mod (F_ACx A C x)"
    unfolding G_ACx_def G_f_def by (auto simp add: algebra_simps)
  hence "2*G_ACx A C x mod (F_ACx A C x) = (2-4*(A+2)*(A-2)^2*E_ACx A C x^2) mod (F_ACx A C x)"
    by auto
  hence "2*G_ACx A C x mod (F_ACx A C x) = (2-4*(A^2-4)*E_ACx A C x^2 * (A-2)) mod (F_ACx A C x)"
    by (auto simp add: algebra_simps power2_eq_square)
  hence "2*G_ACx A C x mod (F_ACx A C x) = (2-(F_ACx A C x-1) * (A-2)) mod (F_ACx A C x)"
    unfolding F_ACx_def F_f_def by auto
  hence "2*G_ACx A C x mod (F_ACx A C x) = (A - (A-2)*F_ACx A C x) mod (F_ACx A C x)"
    by (auto simp add: algebra_simps)
  hence A_eq_2G_modF:  "2*G_ACx A C x mod (F_ACx A C x) = A mod (F_ACx A C x)"
    by (metis add.commute diff_add_cancel mod_mult_self3)

  hence "\<psi>_int A t mod (F_ACx A C x) = \<psi>_int (2*G_ACx A C x) t mod (F_ACx A C x)"
    using lucas_modN_int[of A "F_ACx A C x" "2*G_ACx A C x" t] assms A_eq_2G_modF FBe1 by auto
  hence eq_modF: "\<psi>_int A t mod (F_ACx A C x) = \<psi>_int A s mod (F_ACx A C x)"
    using t_def s_def H_eqC_modF by auto
  have "4*F_ACx A C x = (A^2-4)*(4*E_ACx A C x)^2 +4"
    unfolding F_ACx_def F_f_def power2_eq_square[of 4] power_mult_distrib[of 4 "E_ACx A C x" 2] by auto
  hence "4*F_ACx A C x = ((abs A)^2-4)*(abs (4*E_ACx A C x))^2 +4" by auto
  hence "\<chi> (abs A) n^2 = 4*F_ACx A C x" using lucas_pell_part3[of "abs A" n] \<psi>_A_n_eq_4E by auto
  hence "4*k*k dvd 4*F_ACx A C x" using k_def power2_eq_square[of "2*k"] by auto
  hence "k dvd F_ACx A C x" by auto
  hence "\<psi>_int A t mod k = \<psi>_int A s mod k" using eq_modF by (metis mod_mod_cancel)
  hence "s mod (2*int n) = t mod (2*int n) \<or> (s+t) mod (2*int n) = 0 mod (2*int n) \<and> (2*int n dvd 4*int n)"
    using k_def2 assms nB3 A_B2 sun_lemma10_dir_int[of A n k s t] by auto
  hence t_pm_s_mod_2n: "t mod (2*int n) = s mod (2*int n) \<or> t mod (2*int n) = (- s) mod (2*int n)"
    using mod_diff_cong[of "s + t" "2*int n" 0 s s] by auto

  have C2_dvd_4E: "C^2 dvd abs (4*E_ACx A C x)" unfolding E_ACx_def E_f_def by auto
  hence "\<psi>_int A s^2 dvd \<psi> (abs A) n" using s_def \<psi>_A_n_eq_4E by auto
  hence "\<psi> (abs A) (nat (abs s))^2 dvd \<psi> (abs A) n" using eq_\<psi>_int[of A s] A_B2
    by (metis abs_of_nat int_one_le_iff_zero_less int_ops(1) not_numeral_le_zero power2_abs
        verit_comp_simplify1(3) verit_la_disequality verit_la_generic zero_less_abs_iff)
  hence "\<psi> (abs A) (nat (abs s)) dvd n" using sun_lemma7[of "abs A" "nat (abs s)" n] A_pos sB1
    by auto
  hence "\<psi>_int A s dvd n" using eq_\<psi>_int[of A s] A_B2 by (smt (verit) nat_abs_dvd_iff)
  hence "C dvd n" using s_def by auto
  hence "2*C dvd 2*int n" by auto
  hence t_pm_s_mod_2C: "t mod (2*C) = s mod (2*C) \<or> t mod (2*C) = (- s) mod (2*C)" 
    using t_pm_s_mod_2n div_mod[of "2*C" "2*int n" t s] div_mod[of "2*C" "2*int n" t "- s"] by auto
  have "F_ACx A C x = 4*(A^2-4)*((C*D_f A C * x)*C)^2+1"
    unfolding F_ACx_def F_f_def E_ACx_def E_f_def using power2_eq_square[of C]
    by (auto simp add: algebra_simps)
  hence "F_ACx A C x = ((A^2-4)*(C*D_f A C * x)^2*2*C)*(2*C)+1"
    using power_mult_distrib[of "C*D_f A C*x" C 2] power2_eq_square[of C]
    by (auto simp add: algebra_simps)
  hence F_eq_1_mod_2C: "F_ACx A C x mod (2*C) = 1 mod (2*C)" by (metis mod_mult_self3)
  have "2*C dvd 4*E_ACx A C x" unfolding E_ACx_def E_f_def using power2_eq_square[of C] by auto
  hence TwoC_dvd_4E: "2*C dvd ((A+2)*(A-2)^2*E_ACx A C x)*(4*E_ACx A C x)" by auto
  have "2*G_ACx A C x =
      2 + (D_f A C * F_ACx A C x)*(2*C) - ((A+2)*(A-2)^2*E_ACx A C x)*(4*E_ACx A C x)"
    unfolding G_ACx_def G_f_def using power2_eq_square[of "E_ACx A C x"]
    by (auto simp add: algebra_simps)
  hence "2*G_ACx A C x mod (2*C) = (2 - ((A+2)*(A-2)^2*E_ACx A C x)*(4*E_ACx A C x)) mod (2*C)"
    by (metis mod_diff_left_eq mod_mult_self1)
  hence TwoG_eq_2_mod_2C: "2*G_ACx A C x mod (2*C) = 2 mod (2*C)"
    using TwoC_dvd_4E by (metis minus_mod_self2 mod_mod_cancel)
  have "F_ACx A C x mod 2 = 1 mod 2" unfolding F_ACx_def F_f_def
    by (metis even_mult_iff even_numeral mod_mod_cancel mod_mult_self4)
  hence "((2*y-1)*F_ACx A C x + 1) mod 2 = 0 mod 2" by presburger
  hence "2 dvd ((2*y-1)*F_ACx A C x + 1)" by presburger
  hence fact1: "(2*C) dvd ((2*y-1)*F_ACx A C x + 1)*C" by auto
  have "H_ABCxy A B C x y = ((2*y-1)*F_ACx A C x +1)*C + B*F_ACx A C x"
    unfolding H_ABCxy_def H_f_def by (auto simp add: algebra_simps)
  hence "H_ABCxy A B C x y mod (2*C)= B*F_ACx A C x mod (2*C)" using fact1 by fastforce
  hence H_eq_B_mod_2C: "H_ABCxy A B C x y mod (2*C)= B mod (2*C)"
    using F_eq_1_mod_2C mod_mult_cong[of B "2*C" B "F_ACx A C x" 1] by auto
  have "\<psi>_int (2*G_ACx A C x) t mod (2*C) = \<psi>_int 2 t mod (2*C)"
    using TwoG_eq_2_mod_2C lucas_modN_int[of "2*G_ACx A C x" "2*C" 2 t] assms C_nonzero by auto
  hence "\<psi>_int (2*G_ACx A C x) t mod (2*C) = (- 1) ^ (if 0 \<le> t then 0 else 1) * \<bar>t\<bar> mod (2*C)"
    using \<psi>_int_def[of 2 t] lucas_A_eq_2[of "nat (abs t)"]
    by (simp add: \<open>\<psi> 2 (nat \<bar>t\<bar>) = int (nat \<bar>t\<bar>)\<close> \<open>\<psi>_int (2 * G_ACx A C x) t mod (2 * C) = \<psi>_int 2 t mod (2 * C)\<close>
        \<open>\<psi>_int 2 t = (- 1) ^ (if 0 \<le> t then 0 else 1) * \<psi> 2 (nat \<bar>t\<bar>)\<close> nat_0_le)
  hence \<psi>_2G_eq_t_mod_2C: "\<psi>_int (2*G_ACx A C x) t mod (2*C) = t mod (2*C)" by auto
  hence B_pm_s_mod_2C: "B mod (2*C) = s mod (2*C) \<or> B mod (2*C) = (-s) mod (2*C)"
    using H_eq_B_mod_2C t_def t_pm_s_mod_2C by auto
  hence "B mod (2*C) = s mod (2*C)"
  proof -
    consider (plus) "B mod (2*C) = s mod (2*C)" | (minus) "B mod (2*C) = (-s) mod (2*C)"
      using B_pm_s_mod_2C by auto
    then show ?thesis
    proof (cases)
      case plus
      then show ?thesis by auto
    next
      case minus
      hence "(B+s) mod (2*C) = 0 mod (2*C)" using mod_add_cong[of B "2*C" "-s" s s] by auto
      then obtain z where "B+s = 2*C*z" by auto
      hence z_def: "B = 2*C*z - s" by auto
      consider (0) "z = 0" | (n0) "abs z > 0" by linarith
      then show ?thesis
      proof (cases)
        case 0
        hence B_eq_ms: "B = - s" using z_def by auto
        have "(C - B) mod (A-2) = 0 mod (A-2)" using assms by auto
        hence "B mod (A-2) = C mod (A-2)" using mod_add_cong[of "C-B" "A-2" 0 B B] by auto
        hence "B mod (A-2) = \<psi>_int A s mod (A-2) \<and> A mod (A-2) = 2 mod (A-2)"
          using s_def by (smt (z3) minus_mod_self2)
        hence fact3: "B mod (A-2) = \<psi>_int 2 s mod (A-2)"
          using lucas_modN_int[of A "A-2" 2 s] by auto
        hence "B mod (A-2) = s mod (A-2)"
        proof -
          have \<psi>2: "\<psi> 2 q = int q" for q
          proof (induction q rule: \<psi>_induct)
            case 0
            then show ?case by auto
          next
            case 1
            then show ?case by auto
          next
            case (sucsuc n)
            then show ?case by auto
          qed
          have "(-1)^(if 0 \<le> s then 0 else 1)*int (nat (abs s)) = s" by auto
          then show ?thesis using \<psi>_int_def[of 2 s] \<psi>2[of "nat (abs s)"] fact3 by presburger
        qed
        hence "(-s) mod (A-2) = s mod (A-2)" using B_eq_ms by auto
        hence "2*(-s) mod (A-2) = 0 mod (A-2)" using mod_diff_cong[of "-s" "A-2" s s s] by auto
        hence "(A-2) dvd 2*(-s)" by presburger
        hence "(A-2) dvd 2*B" using B_eq_ms by simp
        hence "abs (A-2) < abs (2*B)" using assms A_B2 dvd_imp_le_int[of "2*B" "A-2"] by linarith
        hence "abs A - 2 < 2*abs B" by auto
        hence "abs A - 1 \<le> 2*abs B" by auto
        hence "abs A - 1 < abs A - 2" using assms by auto
        then show ?thesis by auto
      next
        case n0
        have "abs B \<ge> abs (2*C*z) - abs s" using z_def by auto
        hence "abs B \<ge> 2*abs C * abs z - abs s" by auto
        hence "abs B \<ge> 2*abs C - abs s" using n0 mult_left_mono[of 1 "abs z" "2*abs C"] by linarith
        hence "abs B \<ge> abs C + \<psi> (abs A) (nat (abs s)) - abs s" using eq_\<psi>_int[of A s] s_def A_B2
          by auto
        hence "abs B \<ge> abs C" using lucas_monotone3[of A "nat (abs s)"] A_B2
          by (smt (verit, ccfv_SIG) C_Bigger_A assms(2) le_add1 lucas_monotone3 nat_le_iff of_nat_1 of_nat_add)
        hence "abs B \<ge> abs A" using C_Bigger_A by auto
        then show ?thesis using assms by auto
      qed
    qed
  qed
  hence "(B - s) mod (2*C) = 0 mod (2*C)" using mod_diff_cong[of B "2*C" s s s] by auto
  then obtain z where z_def: "B- s = 2*C*z" by auto
  have "B=s"
  proof -
    consider (0) "z=0" | (n0) "abs z \<ge> 1" by linarith
    then show ?thesis
    proof (cases)
      case 0
      then show ?thesis using z_def by auto
    next
      case n0
      have "abs B \<ge> abs (2*C*z) - abs s" using z_def by auto
      hence "abs B \<ge> 2*abs C * abs z - abs s" by auto
      hence "abs B \<ge> 2*abs C - abs s" using n0 mult_left_mono[of 1 "abs z" "2*abs C"] by linarith
      hence "abs B \<ge> abs C + \<psi> (abs A) (nat (abs s)) - abs s" using eq_\<psi>_int[of A s] s_def A_B2
        by auto
      hence "abs B \<ge> abs C" using lucas_monotone3[of A "nat (abs s)"] A_B2
        by (smt (verit, ccfv_SIG) C_Bigger_A assms(2) le_add1 lucas_monotone3 nat_le_iff of_nat_1 of_nat_add)
      hence "abs B \<ge> abs A" using C_Bigger_A by auto
      then show ?thesis using assms by auto
    qed
  qed
  then show ?thesis using s_def by auto
qed


end
