subsection "Representing $\\mathbb{Z}_{F_n}$"

theory Z_mod_Fermat
  imports
    Z_mod_power_of_2
    "../NTT_Rings/FNTT_Rings"
    "../Preliminaries/Schoenhage_Strassen_Preliminaries"
    "Karatsuba.Estimation_Method"
begin

lemma to_nat_replicate_True2:
  assumes "Nat_LSBF.to_nat xs = 2 ^ (length xs) - 1"
  shows "xs = replicate (length xs) True"
proof (intro iffD2[OF list_is_replicate_iff], rule ccontr)
  assume "\<not> (\<forall>i\<in>{0..<length xs}. xs ! i = True)"
  then obtain i where "i < length xs" "xs ! i = False" by auto
  then obtain xs1 xs2 where "xs = xs1 @ False # xs2"
    by (metis(full_types) id_take_nth_drop)
  then have "Nat_LSBF.to_nat xs < Nat_LSBF.to_nat (xs1 @ True # xs2)"
    using change_bit_ineq[of xs1 xs1 xs2] by argo
  also have "... \<le> 2 ^ (length (xs1 @ True # xs2)) - 1"
    by (intro to_nat_length_upper_bound)
  also have "... = 2 ^ (length xs) - 1"
    using \<open>xs = xs1 @ False # xs2\<close> by simp
  finally show False using assms by simp
qed

lemma residue_ring_pow: "n > 1 \<Longrightarrow> a [^]\<^bsub>residue_ring n\<^esub> b = (a ^ b) mod n"
  by (induction b) (simp_all add: residue_ring_def mod_mult_right_eq mult.commute)

lemma (in residues) pow_nat_eq:
"a [^]\<^bsub>R\<^esub> (n :: nat) = a ^ n mod m"
  using R_m_def m_gt_one residue_ring_pow by blast

locale int_lsbf_fermat =
  fixes k :: nat
begin

abbreviation n where "n \<equiv> (2::nat) ^ (2 ^ k) + 1"

lemma n_positive[simp]: "n > 0" by simp
lemma n_gt_1[simp]: "n > 1" by simp
lemma n_gt_2[simp]: "n > 2"
  by (metis add_less_mono1 nat_1_add_1 one_less_numeral_iff one_less_power pos2 semiring_norm(76) zero_less_power)  

definition Fn where "Fn \<equiv> residue_ring (int n)"

sublocale residues n Fn
  apply unfold_locales
  subgoal by simp
  subgoal by (rule Fn_def)
  done

definition fermat_non_unique_carrier where
"fermat_non_unique_carrier \<equiv> {xs :: nat_lsbf. length xs = 2 ^ (k + 1)}"

lemma fermat_non_unique_carrierI[intro]:
"length xs = 2 ^ (k + 1) \<Longrightarrow> xs \<in> fermat_non_unique_carrier"
  unfolding fermat_non_unique_carrier_def by simp

lemma fermat_non_unique_carrierE[elim]:
  "xs \<in> fermat_non_unique_carrier \<Longrightarrow> (length xs = 2 ^ (k + 1) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding fermat_non_unique_carrier_def by simp

lemma two_pow_half_carrier_length[simp]: "(int 2 ^ (2 ^ k)) mod n = -1 mod n"
  apply simp
  using zmod_minus1[of "int n"] n_positive
  by (metis add_diff_cancel_left' diff_eq_eq of_nat_0_less_iff of_nat_numeral pos2 zero_less_power zless_add1_eq zmod_minus1)

lemma two_pow_half_carrier_length_neq_1: "2 ^ (2 ^ k) mod n \<noteq> 1"
  by simp

lemma two_pow_carrier_length[simp]: "(2::nat) ^ (2 ^ (k + 1)) mod n = 1"
proof -
  have "int 2 ^ (2 ^ (k + 1)) mod n = 1"
  proof -
    have "int 2 ^ (2 ^ (k + 1)) mod n = ((int 2) ^ (2 * 2 ^ k)) mod n"
      by simp
    also have "... = ((int 2) ^ (2 ^ k)) ^ 2 mod n"
      using power_mult[of "int 2" "2 ^ k" 2]
      by (simp add: mult.commute)
    also have "... = (int 2 ^ (2 ^ k) * int 2 ^ (2 ^ k)) mod n"
      by (simp add: power2_eq_square)
    also have "... = (((int 2 ^ (2 ^ k)) mod n) * ((int 2 ^ (2 ^ k)) mod n)) mod n"
      by simp
    also have "(int 2 ^ (2 ^ k)) mod n = -1 mod n"
      using two_pow_half_carrier_length .
    finally have "int 2 ^ (2 ^ (k + 1)) mod n = int 1 mod n"
      by (simp add: mod_simps)
    thus ?thesis by simp
  qed
  then show ?thesis
    by (metis int_ops(2) of_nat_eq_iff of_nat_power zmod_int)
qed

lemma two_pow_half_carrier_length_residue_ring[simp]:
"(2::int) [^]\<^bsub>Fn\<^esub> (2::nat) ^ k = \<ominus>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub>"
proof -
  have "(2::int) [^]\<^bsub>Fn\<^esub> (2::nat) ^ k = (2::int) ^ ((2::nat) ^ k) mod n"
    by (intro pow_nat_eq)
  also have "... = - 1 mod n" using two_pow_half_carrier_length by simp
  also have "... = \<ominus>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub>"
    using res_neg_eq res_one_eq by algebra
  finally show ?thesis .
qed

lemma two_pow_carrier_length_residue_ring[simp]:
  "(2::int) [^]\<^bsub>Fn\<^esub> (2::nat) ^ (k + 1) = \<one>\<^bsub>Fn\<^esub>"
proof -
  have "(2::int) [^]\<^bsub>Fn\<^esub> (2::nat) ^ (k + 1) = (2::int) ^ ((2::nat) ^ (k + 1)) mod n"
    by (intro pow_nat_eq)
  also have "... = 1" using two_pow_carrier_length zmod_int
    by (metis int_exp_hom int_ops(2) int_ops(3))
  also have "... = \<one>\<^bsub>Fn\<^esub>" by (simp only: res_one_eq)
  finally show ?thesis .
qed

corollary two_is_unit: "2 \<in> Units Fn"
  apply (intro pow_one_imp_unit[of "2 ^ (k + 1)"])
  subgoal by simp
  subgoal using res_carrier_eq by (simp add: self_le_power)
  subgoal using two_pow_carrier_length_residue_ring .
  done

corollary two_in_carrier: "2 \<in> carrier Fn"
  using Units_closed[OF two_is_unit] .

lemma nat_mod_eqE: "(a::nat) mod m = b mod m \<Longrightarrow> \<exists>i j. a + i * m = b + j * m"
proof -
  assume "a mod m = b mod m"
  then have "int a mod int m = int b mod int m" using zmod_int by metis
  then obtain l where "int a = int b + l * int m" by (metis mod_eqE mult.commute)
  define i j where "i = (if l \<ge> 0 then 0 else nat (- l))" "j = (if l \<ge> 0 then nat l else 0)"
  then have "int a + int i * int m = int b + int j * int m"
    using \<open>int a = int b + l * int m\<close> by simp
  then have "a + i * m = b + j * m" by (metis int_ops(7) nat_int_add)
  then show ?thesis by blast
qed

corollary pow_mod_carrier_length:
  assumes "(a::nat) mod 2 ^ (k + 1) = b mod 2 ^ (k + 1)"
  shows "2 [^]\<^bsub>Fn\<^esub> a = 2 [^]\<^bsub>Fn\<^esub> b"
proof -
  from assms obtain i j where 0: "a + i * 2 ^ (k + 1) = b + j * 2 ^ (k + 1)"
    using nat_mod_eqE by blast
  have "2 [^]\<^bsub>Fn\<^esub> a = 2 [^]\<^bsub>Fn\<^esub> a \<otimes>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1))) [^]\<^bsub>Fn\<^esub> i"
    using two_pow_carrier_length_residue_ring two_in_carrier nat_pow_closed
    using nat_pow_one by algebra
  also have "... = 2 [^]\<^bsub>Fn\<^esub> (a + i * 2 ^ (k + 1))"
    using nat_pow_pow nat_pow_mult two_in_carrier
    using mult.commute by metis
  also have "... = 2 [^]\<^bsub>Fn\<^esub> (b + j * 2 ^ (k + 1))"
    using 0 by argo
  also have "... = 2 [^]\<^bsub>Fn\<^esub> b \<otimes>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1))) [^]\<^bsub>Fn\<^esub> j"
    using nat_pow_pow nat_pow_mult two_in_carrier
    using mult.commute by metis
  also have "... = 2 [^]\<^bsub>Fn\<^esub> b"
    using two_pow_carrier_length_residue_ring two_in_carrier nat_pow_closed
    using nat_pow_one by algebra
  finally show ?thesis .
qed
lemma two_powers_trivial:
  assumes "s \<le> 2 ^ k"
  shows "2 [^]\<^bsub>Fn\<^esub> s = 2 ^ s"
proof -
  from assms have "2 ^ s \<le> int n - 1" by simp
  then have "2 ^ s < int n" using n_positive by linarith
  then have "2 ^ s = 2 ^ s mod int n" by simp
  also have "... = 2 [^]\<^bsub>Fn\<^esub> s" using pow_nat_eq by simp
  finally show ?thesis by argo
qed

lemma two_powers_Units:
  assumes "s \<le> 2 ^ k"
  shows "2 ^ s \<in> Units Fn"
  unfolding two_powers_trivial[OF assms, symmetric]
  by (intro Units_pow_closed two_is_unit)
corollary two_powers_in_carrier:
  assumes "s \<le> 2 ^ k"
  shows "2 ^ s \<in> carrier Fn"
  using assms two_powers_Units Units_closed by simp

lemma two_powers_half_carrier_length_residue_ring[simp]:
  assumes "i + s = k"
  shows "(2 ^ 2 ^ i) [^]\<^bsub>Fn\<^esub> (2::nat) ^ s = \<ominus>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub>"
proof -
  from assms have "i \<le> k" by simp
  then have "(2 ^ 2 ^ i) [^]\<^bsub>Fn\<^esub> (2::nat) ^ s =
    (2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ i)) [^]\<^bsub>Fn\<^esub> (2::nat) ^ s"
    using two_powers_trivial[of "2 ^ i", symmetric] by simp
  also have "... = 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (i + s))" 
    using monoid.nat_pow_pow[OF _ two_in_carrier] cring
    using power_add[symmetric, of "2::nat" i s]
    using monoid_axioms by auto
  also have "... = \<ominus>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub>"
    using \<open>i + s = k\<close> two_pow_half_carrier_length_residue_ring by argo
  finally show ?thesis .
qed

interpretation z_mod_fermat_unit_group: group "units_of Fn"
  by (rule units_group)


lemma inv_of_2[simp]:
  "inv\<^bsub>Fn\<^esub> 2 = 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1) - 1)"
proof -
  have "\<one>\<^bsub>Fn\<^esub> = 2 \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1) - 1)"
    by (metis two_is_unit two_pow_carrier_length_residue_ring Units_closed Units_r_inv inv_root_of_unity root_of_unityI zero_less_numeral zero_less_power)
  moreover have "\<one>\<^bsub>Fn\<^esub> = 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1) - 1) \<otimes>\<^bsub>Fn\<^esub> 2"
   by (metis two_is_unit two_pow_carrier_length_residue_ring Units_closed Units_l_inv inv_root_of_unity root_of_unityI zero_less_numeral zero_less_power)
  ultimately show "inv\<^bsub>Fn\<^esub> 2 = 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1) - 1)"
    using less_2_cases_iff two_pow_carrier_length_residue_ring two_in_carrier inv_root_of_unity root_of_unityI by presburger
qed

lemma inv_of_2_powers:
  assumes "s \<le> 2 ^ k"
  shows "inv\<^bsub>Fn\<^esub> (2 ^ s) = 2 [^]\<^bsub>Fn\<^esub> (2 ^ (k + 1) - s)"
proof (cases "s = 0")
  case True
  then show ?thesis
    using inv_one res_one_eq
    using two_pow_carrier_length_residue_ring
    by simp
next
  case False
  then have "s > 0" by simp
  interpret m : multiplicative_subgroup Fn "Units Fn" "units_of Fn"
    apply unfold_locales
    subgoal by simp
    subgoal by (simp add: units_of_def)
    done
  have "inv\<^bsub>Fn\<^esub> (2 ^ s) = inv\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s)"
    using two_powers_trivial[OF \<open>s \<le> 2 ^ k\<close>] by argo
  also have "... = (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> s"
    using two_is_unit group.nat_pow_inv[OF m.M_group] m.inv_eq m.M_group m.carrier_M
    using m.nat_pow_eq Units_pow_closed by algebra
  also have "... = (2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (k + 1) - 1)) [^]\<^bsub>Fn\<^esub> s"
    using inv_of_2
    by argo
  also have "... = 2 [^]\<^bsub>Fn\<^esub> (((2::nat) ^ (k + 1) - 1) * s)"
    using two_in_carrier nat_pow_pow by presburger
  also have "((2::nat) ^ (k + 1) - 1) * s = (2::nat) ^ (k + 1) * s - s"
    using diff_mult_distrib by simp
  also have "... = 2 ^ (k + 1) * (s - 1) + 2 ^ (k + 1) - s"
    using \<open>s > 0\<close> by (metis add.commute mult.commute mult_eq_if zero_less_iff_neq_zero)
  also have "... = 2 ^ (k + 1) * (s - 1) + (2 ^ (k + 1) - s)"
    apply (intro diff_add_assoc) using assms by simp
  also have "2 [^]\<^bsub>Fn\<^esub> (2 ^ (k + 1) * (s - 1) + (2 ^ (k + 1) - s)) =
    2 [^]\<^bsub>Fn\<^esub> (2 ^ (k + 1) - s)"
    apply (intro pow_mod_carrier_length) by simp
  finally show ?thesis .
qed

lemma inv_pow_mod_carrier_length:
  assumes "(a::nat) mod 2 ^ (k + 1) = b mod 2 ^ (k + 1)"
  shows "(inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> a = (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> b"
  unfolding inv_of_2 nat_pow_pow[OF two_in_carrier]
  apply (intro pow_mod_carrier_length)
  using assms mod_mult_cong by blast

lemma
  assumes "m > 0"
  shows "\<exists>i j. (a::nat) = j + i * m \<and> j < m"
  using mod_div_mult_eq[of a m, symmetric] pos_mod_bound[of m a] assms by blast

corollary two_powers: "(2::nat) ^ a mod n = (2::nat) ^ (a mod (2 ^ (k + 1))) mod n"
proof -
  define i where "i = a mod 2 ^ (k + 1)"
  define j where "j = a div 2 ^ (k + 1)"
  have "a = i + j * 2 ^ (k + 1)" using mod_div_mult_eq[of a "2 ^ (k + 1)"] i_def j_def
    by simp
  hence "(2::nat) ^ a mod n = 2 ^ i * (2 ^ (2 ^ (k + 1))) ^ j mod n"
    using power_add[of "2::nat" i "j * 2 ^ (k + 1)"]
    using power_mult[of "2::nat" "2 ^ (k + 1)" j]
    using mult.commute[of j "2 ^ (k + 1)"]
    by argo
  also have "... = 2 ^ i * ((2 ^ (2 ^ (k + 1))) ^ j mod n) mod n"
    using mod_mult_right_eq by metis
  also have "... = 2 ^ i * ((2 ^ (2 ^ (k + 1)) mod n) ^ j mod n) mod n"
    using power_mod by metis
  also have "... = 2 ^ i * ((1::nat) ^ j mod n) mod n"
    using two_pow_carrier_length by simp
  also have "... = 2 ^ i mod n" by simp
  finally show ?thesis using i_def by simp
qed

lemma fermat_carrier_length[simp]: "xs \<in> fermat_non_unique_carrier \<Longrightarrow> length xs = 2 ^ (k + 1)"
  unfolding fermat_non_unique_carrier_def by simp

fun to_residue_ring :: "nat_lsbf \<Rightarrow> int" where
"to_residue_ring xs = int (Nat_LSBF.to_nat xs) mod int n"
fun from_residue_ring :: "int \<Rightarrow> nat_lsbf" where
"from_residue_ring x = fill (2 ^ (k + 1)) (Nat_LSBF.from_nat (nat x))"

lemma to_residue_ring_in_carrier[simp]: "to_residue_ring xs \<in> carrier Fn"
  using zmod_int[of _ n, symmetric]
  by (simp add: res_carrier_eq)

lemma to_residue_ring_eq_to_nat: "Nat_LSBF.to_nat xs < n \<Longrightarrow> to_residue_ring xs = int (Nat_LSBF.to_nat xs)"
  using zmod_int
  by (metis to_residue_ring.simps mod_less)

(* calculates a * 2 ^ k, where a is in the fermat carrier, k a natural number. *)
definition multiply_with_power_of_2 :: "nat_lsbf \<Rightarrow> nat \<Rightarrow> nat_lsbf" where
"multiply_with_power_of_2 xs m = rotate_right m xs"

definition divide_by_power_of_2 :: "nat_lsbf \<Rightarrow> nat \<Rightarrow> nat_lsbf" where
"divide_by_power_of_2 xs m = rotate_left m xs"

lemma length_multiply_with_power_of_2[simp]: "length (multiply_with_power_of_2 xs m) = length xs"
  unfolding multiply_with_power_of_2_def by simp

lemma length_divide_by_power_of_2[simp]: "length (divide_by_power_of_2 xs m) = length xs"
  unfolding divide_by_power_of_2_def by simp

lemma (in euclidean_semiring_cancel) sum_list_mod: "(\<Sum>i \<leftarrow> xs. (f i mod m)) mod m = (\<Sum>i \<leftarrow> xs. f i) mod m"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "(\<Sum>i \<leftarrow> (a # xs). f i) mod m = (f a + (\<Sum>i \<leftarrow> xs. f i)) mod m"
    by simp
  also have "... = (f a mod m + (\<Sum>i \<leftarrow> xs. f i) mod m) mod m"
    using mod_add_eq[symmetric, of "f a"] by simp
  also have "... = (f a mod m + (\<Sum>i \<leftarrow> xs. f i mod m) mod m) mod m"
    using Cons.IH by argo
  also have "... = (f a mod m + (\<Sum>i \<leftarrow> xs. f i mod m)) mod m"
    using mod_add_right_eq by blast
  also have "... = (\<Sum>i \<leftarrow> (a # xs). f i mod m) mod m"
    by simp
  finally show ?case by argo
qed

lemma (in euclidean_semiring_cancel) sum_list_mod':
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i mod m = g i mod m"
  shows "(\<Sum>i \<leftarrow> xs. f i) mod m = (\<Sum>i \<leftarrow> xs. g i) mod m"
proof -
  have "(\<Sum>i \<leftarrow> xs. f i) mod m = (\<Sum>i \<leftarrow> xs. f i mod m) mod m"
    by (intro sum_list_mod[symmetric])
  also have "... = (\<Sum>i \<leftarrow> xs. g i mod m) mod m"
    apply (intro_cong "[cong_tag_1 (\<lambda>i. i mod m)]")
    apply (intro_cong "[cong_tag_1 sum_list]" more: map_cong refl)
    using assms by assumption
  also have "... = (\<Sum>i \<leftarrow> xs. g i) mod m"
    by (intro sum_list_mod)
  finally show ?thesis .
qed

lemma multiply_with_power_of_2_correct': "xs \<in> fermat_non_unique_carrier \<Longrightarrow> Nat_LSBF.to_nat (multiply_with_power_of_2 xs m) mod n = Nat_LSBF.to_nat xs * 2 ^ m mod n \<and> multiply_with_power_of_2 xs m \<in> fermat_non_unique_carrier"
proof (intro conjI)
  assume "xs \<in> fermat_non_unique_carrier"
  then have length_xs: "length xs = 2 ^ (k + 1)" by simp
  then have "length xs > 0" by simp

  let ?m = "length xs - m mod length xs"

  define ys zs where "ys = take ?m xs" "zs = drop ?m xs"
  then have "xs = ys @ zs"
    and length_ys: "length ys = ?m"
    and length_zs: "length zs = m mod length xs"
    using \<open>length xs = 2 ^ (k + 1)\<close> by simp_all
  
  have 1: "Nat_LSBF.to_nat xs = Nat_LSBF.to_nat ys + 2 ^ ?m * Nat_LSBF.to_nat zs" (is "_ = ?y + _ * ?z")
    apply (unfold \<open>xs = ys @ zs\<close> to_nat_app)
    apply (unfold \<open>xs = ys @ zs\<close>[symmetric] length_ys)
    apply (rule refl)
    done

  have 2: "multiply_with_power_of_2 xs m = zs @ ys"
  proof -
    have "multiply_with_power_of_2 xs m = rotate_right (m mod length xs) xs"
      unfolding multiply_with_power_of_2_def
      by (rule rotate_right_conv_mod)
    also have "... = rotate_right (length zs) (ys @ zs)"
      using \<open>xs = ys @ zs\<close> length_zs by simp
    also have "... = zs @ ys"
      by (rule rotate_right_append)
    finally show ?thesis .
  qed
  then have 3: "Nat_LSBF.to_nat (multiply_with_power_of_2 xs m)
    = ?z + 2 ^ (m mod length xs) * ?y"
    by (simp add: to_nat_app length_zs)

  from 1 have "Nat_LSBF.to_nat xs * 2 ^ m mod n = (?y + 2 ^ ?m * ?z) * 2 ^ m mod n"
    by argo
  also have "... = (?y + 2 ^ ?m * ?z) * (2 ^ m mod n) mod n"
    by (simp add: mod_simps)
  also have "... = (?y + 2 ^ ?m * ?z) * (2 ^ (m mod length xs) mod n) mod n"
    using length_xs two_powers by algebra
  also have "... = (?y + 2 ^ ?m * ?z) * 2 ^ (m mod length xs) mod n"
    by (simp add: mod_simps)
  also have "... = (?y * 2 ^ (m mod length xs) + 2 ^ (?m + (m mod length xs)) * ?z) mod n"
    by (simp add: algebra_simps power_add)
  also have "... = (?y * 2 ^ (m mod length xs) + 2 ^ length xs * ?z) mod n"
    by (simp add: length_xs)
  also have "... = (?y * 2 ^ (m mod length xs) + (2 ^ length xs mod n) * ?z mod n) mod n"
    by (simp add: mod_simps)
  also have "... = (?y * 2 ^ (m mod length xs) + 1 * ?z mod n) mod n"
    by (simp only: length_xs two_pow_carrier_length)
  also have "... = (?z + 2 ^ (m mod length xs) * ?y) mod n"
    by (simp add: mod_simps algebra_simps)
  also have "... = Nat_LSBF.to_nat (multiply_with_power_of_2 xs m) mod n"
    using 3 by argo
  finally show "Nat_LSBF.to_nat (multiply_with_power_of_2 xs m) mod n = Nat_LSBF.to_nat xs * 2 ^ m mod n"
    by argo

  have "length (multiply_with_power_of_2 xs m) = length xs"
    using 2 \<open>xs = ys @ zs\<close> by simp
  then show "multiply_with_power_of_2 xs m \<in> fermat_non_unique_carrier"
    apply (intro fermat_non_unique_carrierI)
    using length_xs by argo
qed

corollary multiply_with_power_of_2_closed:
  assumes "xs \<in> fermat_non_unique_carrier"
  shows "multiply_with_power_of_2 xs m \<in> fermat_non_unique_carrier"
  by (intro conjunct2[OF multiply_with_power_of_2_correct'] assms)

corollary multiply_with_power_of_2_correct:
  assumes "xs \<in> fermat_non_unique_carrier"
  shows "to_residue_ring (multiply_with_power_of_2 xs m) = to_residue_ring xs \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> m"
proof -
  have "to_residue_ring (multiply_with_power_of_2 xs m)
       = int (Nat_LSBF.to_nat (multiply_with_power_of_2 xs m) mod n)"
    using zmod_int by simp
  also have "... = int (Nat_LSBF.to_nat xs * 2 ^ m mod n)"
    using multiply_with_power_of_2_correct'[OF assms] by simp
  also have "... = (int (Nat_LSBF.to_nat xs)) * (2 ^ m) mod int n"
    using zmod_int by simp
  also have "... = (int (Nat_LSBF.to_nat xs) mod int n) * ((2 ^ m) mod int n) mod int n"
    by (simp add: mod_mult_eq)
  also have "... = (to_residue_ring xs) \<otimes>\<^bsub>Fn\<^esub> ((2 ^ m) mod int n)"
    using res_mult_eq by simp
  also have "(2 ^ m) mod int n = 2 [^]\<^bsub>Fn\<^esub> m"
    using pow_nat_eq by simp
  finally show ?thesis .
qed

lemma
  assumes "xs \<in> fermat_non_unique_carrier"
  shows divide_by_power_of_2_correct: "to_residue_ring (divide_by_power_of_2 xs m) = to_residue_ring xs \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> m"
    and divide_by_power_of_2_closed: "divide_by_power_of_2 xs m \<in> fermat_non_unique_carrier"
  unfolding atomize_conj
proof (intro conjI)
  from assms show c: "divide_by_power_of_2 xs m \<in> fermat_non_unique_carrier"
    unfolding fermat_non_unique_carrier_def by simp
  define divxs where "divxs = divide_by_power_of_2 xs m"
  define mulxs where "mulxs = multiply_with_power_of_2 xs m"

  have "multiply_with_power_of_2 divxs m = xs"
    unfolding divxs_def multiply_with_power_of_2_def divide_by_power_of_2_def by simp
  then have "to_residue_ring xs = to_residue_ring (multiply_with_power_of_2 divxs m)"
    by simp
  also have "... = to_residue_ring divxs \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> m"
    apply (intro multiply_with_power_of_2_correct)
    unfolding divxs_def by (rule c)
  finally have "to_residue_ring xs \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> m = to_residue_ring divxs \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> m \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> m"
    by simp
  also have "... = to_residue_ring divxs \<otimes>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> m \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> m)"
    apply (intro m_assoc to_residue_ring_in_carrier nat_pow_closed two_in_carrier)
    using two_is_unit by auto
  also have "(2 [^]\<^bsub>Fn\<^esub> m \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> m) = (2 \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2)) [^]\<^bsub>Fn\<^esub> m"
    apply (intro pow_mult_distrib[symmetric] m_comm two_in_carrier)
    using two_is_unit by auto
  also have "... = \<one>\<^bsub>Fn\<^esub> [^]\<^bsub>Fn\<^esub> m"
    by (intro arg_cong2[where f = "([^]\<^bsub>Fn\<^esub>)"] refl Units_r_inv two_is_unit)
  also have "... = \<one>\<^bsub>Fn\<^esub>" by simp
  also have "to_residue_ring divxs \<otimes>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub> = to_residue_ring divxs"
    by (intro r_one to_residue_ring_in_carrier)
  finally show "to_residue_ring divxs = to_residue_ring xs \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> m" by simp
qed

definition add_fermat where
"add_fermat xs ys = (let zs = add_nat xs ys in if length zs = 2 ^ (k + 1) + 1 then inc_nat (butlast zs) else zs)"

lemma add_fermat_correct':
  assumes "xs \<in> fermat_non_unique_carrier"
  assumes "ys \<in> fermat_non_unique_carrier"
  shows "add_fermat xs ys \<in> fermat_non_unique_carrier \<and> Nat_LSBF.to_nat (add_fermat xs ys) mod n = (Nat_LSBF.to_nat xs + Nat_LSBF.to_nat ys) mod n"
proof -
  define zs where "zs = add_nat xs ys"
  show ?thesis
  proof (cases "length zs = 2 ^ (k + 1) + 1")
    case True
    then have "add_fermat xs ys = inc_nat (butlast zs)"
      using zs_def unfolding add_fermat_def by simp
    then have 1: "Nat_LSBF.to_nat (add_fermat xs ys) = 1 + Nat_LSBF.to_nat (butlast zs)" by (simp add: inc_nat_correct)
    from True obtain zs' where "zs = zs' @ [True]"
      using add_nat_last_bit_True assms zs_def by fastforce
    then have "butlast zs = zs'" by simp
    then have "Nat_LSBF.to_nat (add_fermat xs ys) = 1 + Nat_LSBF.to_nat zs'" using 1 by simp
    moreover have "Nat_LSBF.to_nat zs = Nat_LSBF.to_nat zs' + 2 ^ (2 ^ (k + 1))"
      using \<open>zs = zs' @ [True]\<close> True by (simp add: to_nat_app)
    hence "Nat_LSBF.to_nat zs mod n = (Nat_LSBF.to_nat zs' + 1) mod n"
      using two_pow_carrier_length by (metis mod_add_right_eq)
    ultimately have 2: "Nat_LSBF.to_nat (add_fermat xs ys) mod n = (Nat_LSBF.to_nat xs + Nat_LSBF.to_nat ys) mod n"
      using add_nat_correct[of xs ys] zs_def by auto

    have "length zs' = 2 ^ (k + 1)" using True \<open>zs = zs' @ [True]\<close> by simp

    have "Nat_LSBF.to_nat zs = Nat_LSBF.to_nat xs + Nat_LSBF.to_nat ys" using zs_def by (simp add: add_nat_correct)
    also have "... \<le> (2 ^ length xs - 1) + (2 ^ length ys - 1)"
      using to_nat_length_upper_bound add_le_mono by algebra
    also have "... = (2 ^ (2 ^ (k + 1)) - 1) + (2 ^ (2 ^ (k + 1)) - 1)"
      using assms by simp
    also have "... < (2 ^ (2 ^ (k + 1)) - 1) + (2 ^ (2 ^ (k + 1)))"
      by (meson add_strict_left_mono diff_less pos2 zero_less_one zero_less_power)
    finally have "Nat_LSBF.to_nat zs' < 2 ^ (2 ^ (k + 1)) - 1"
      using \<open>Nat_LSBF.to_nat zs = Nat_LSBF.to_nat zs' + 2 ^ (2 ^ (k + 1))\<close> by simp
    then have "length (inc_nat zs') = length zs'"
      using length_inc_nat' \<open>length zs' = 2 ^ (k + 1)\<close> by simp
    then have "length (add_fermat xs ys) = 2 ^ (k + 1)"
      using \<open>add_fermat xs ys = inc_nat (butlast zs)\<close> \<open>butlast zs = zs'\<close> \<open>length zs' = 2 ^ (k + 1)\<close>
      by simp
    with 2 show ?thesis unfolding fermat_non_unique_carrier_def by simp
  next
    case False
    have "length zs \<ge> 2 ^ (k + 1)"
      using assms zs_def length_add_nat_lower[of xs ys] by simp
    moreover have "length zs \<le> 2 ^ (k + 1) + 1"
      using assms zs_def length_add_nat_upper[of xs ys] by simp
    ultimately have "length zs = 2 ^ (k + 1)" using False by simp
    then have "add_fermat xs ys \<in> fermat_non_unique_carrier"
      unfolding fermat_non_unique_carrier_def add_fermat_def
      by (simp add: Let_def zs_def)
    moreover have "Nat_LSBF.to_nat zs = Nat_LSBF.to_nat xs + Nat_LSBF.to_nat ys"
      by (simp add: zs_def add_nat_correct)
    moreover have "add_fermat xs ys = zs"
      unfolding add_fermat_def using False zs_def by simp
    ultimately show ?thesis by algebra
  qed
qed

corollary add_fermat_closed:
  assumes "xs \<in> fermat_non_unique_carrier"
  assumes "ys \<in> fermat_non_unique_carrier"
  shows "add_fermat xs ys \<in> fermat_non_unique_carrier"
  by (intro conjunct1[OF add_fermat_correct'] assms)

corollary add_fermat_correct:
  assumes "xs \<in> fermat_non_unique_carrier"
  assumes "ys \<in> fermat_non_unique_carrier"
  shows "to_residue_ring (add_fermat xs ys) = to_residue_ring xs \<oplus>\<^bsub>Fn\<^esub> to_residue_ring ys"
proof -
  have "to_residue_ring (add_fermat xs ys) = (int (Nat_LSBF.to_nat xs) + int (Nat_LSBF.to_nat ys)) mod int n"
    using add_fermat_correct'[OF assms]
    by (metis of_nat_add of_nat_mod to_residue_ring.simps)
  also have "... = (int (Nat_LSBF.to_nat xs) mod int n + int (Nat_LSBF.to_nat ys) mod int n) mod int n"
    using mod_add_eq by presburger
  also have "... = (int (Nat_LSBF.to_nat xs mod n) + int (Nat_LSBF.to_nat ys mod n)) mod int n"
    using zmod_int by simp
  also have "... = to_residue_ring xs \<oplus>\<^bsub>Fn\<^esub> to_residue_ring ys"
    by (simp add: res_add_eq zmod_int) 
  finally show ?thesis .
qed

definition subtract_fermat where
  "subtract_fermat xs ys = add_fermat xs (multiply_with_power_of_2 ys (2 ^ k))"

lemma subtract_fermat_correct':
  assumes "xs \<in> fermat_non_unique_carrier"
  assumes "ys \<in> fermat_non_unique_carrier"
  shows "subtract_fermat xs ys \<in> fermat_non_unique_carrier \<and> int (Nat_LSBF.to_nat (subtract_fermat xs ys)) mod n = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod n"
proof -
  from assms(2) have "multiply_with_power_of_2 ys (2 ^ k) \<in> fermat_non_unique_carrier"
    unfolding fermat_non_unique_carrier_def multiply_with_power_of_2_def rotate_right_def by simp
  with assms(1) have 1: "subtract_fermat xs ys \<in> fermat_non_unique_carrier"
    unfolding subtract_fermat_def using add_fermat_correct' by simp
  have "int (Nat_LSBF.to_nat (subtract_fermat xs ys)) mod n = int (Nat_LSBF.to_nat (subtract_fermat xs ys) mod n)"
    using zmod_int by presburger
  also have "... = int ((Nat_LSBF.to_nat xs + Nat_LSBF.to_nat (multiply_with_power_of_2 ys (2 ^ k))) mod n)"
    using add_fermat_correct'
    using \<open>multiply_with_power_of_2 ys (2 ^ k) \<in> fermat_non_unique_carrier\<close>
    using assms(1) subtract_fermat_def by presburger
  also have "... = int ((Nat_LSBF.to_nat xs + Nat_LSBF.to_nat (multiply_with_power_of_2 ys (2 ^ k)) mod n) mod n)"
    by presburger
  also have "... = int ((Nat_LSBF.to_nat xs + (Nat_LSBF.to_nat ys * 2 ^ (2 ^ k)) mod n) mod n)"
    using multiply_with_power_of_2_correct' assms(2) by presburger
  also have "... = (int (Nat_LSBF.to_nat xs) + int (Nat_LSBF.to_nat ys) * (int (2 ^ (2 ^ k)) mod n)) mod n"
    using zmod_int int_ops(7) int_plus
    by (simp add: mod_add_right_eq mod_mult_right_eq)
  also have "... = (int (Nat_LSBF.to_nat xs) + int (Nat_LSBF.to_nat ys) * ((-1) mod n)) mod n"
    using two_pow_half_carrier_length by simp
  also have "... = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod n"
    by (simp add: mod_add_cong mod_mult_right_eq)
  finally show ?thesis using 1 by blast
qed

corollary subtract_fermat_closed:
  assumes "xs \<in> fermat_non_unique_carrier"
  assumes "ys \<in> fermat_non_unique_carrier"
  shows "subtract_fermat xs ys \<in> fermat_non_unique_carrier"
  by (intro conjunct1[OF subtract_fermat_correct'] assms)

corollary subtract_fermat_correct:
  assumes "xs \<in> fermat_non_unique_carrier"
  assumes "ys \<in> fermat_non_unique_carrier"
  shows "to_residue_ring (subtract_fermat xs ys) = to_residue_ring xs \<ominus>\<^bsub>Fn\<^esub> to_residue_ring ys"
proof -
  have "to_residue_ring (subtract_fermat xs ys) = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod int n"
    using zmod_int subtract_fermat_correct' assms by simp
  also have "... = (int (Nat_LSBF.to_nat xs) mod int n - int (Nat_LSBF.to_nat ys) mod int n) mod int n"
    using mod_diff_eq by metis
  also have "... = (int (Nat_LSBF.to_nat xs mod n) - int (Nat_LSBF.to_nat ys mod n)) mod int n"
    using zmod_int by simp
  also have "... = to_residue_ring xs \<ominus>\<^bsub>Fn\<^esub> to_residue_ring ys"
    using residues_minus_eq by (simp add: zmod_int)
  finally show ?thesis .
qed

end

context int_lsbf_fermat begin

definition reduce :: "nat_lsbf \<Rightarrow> nat_lsbf" where
"reduce xs = (let (ys, zs) = split xs in
  if compare_nat zs ys then
    subtract_nat ys zs
  else
    subtract_nat (add_nat (True # replicate (2 ^ k - 1) False @ [True]) ys) zs)"

lemma reduce_correct':
  assumes "xs \<in> fermat_non_unique_carrier"
  shows "Nat_LSBF.to_nat (reduce xs) < n \<and> Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n" and "length (reduce xs) \<le> 2 ^ k + 2"
proof -
  obtain ys zs where "split xs = (ys, zs)" by fastforce
  then have "length ys = 2 ^ k" "length zs = 2 ^ k" using assms by (auto simp: split_def Let_def)
  then have "Nat_LSBF.to_nat ys < n" "Nat_LSBF.to_nat zs < n"
    using to_nat_length_upper_bound
    by (metis add.commute add_strict_increasing le_Suc_ex nat_le_linear nat_zero_less_power_iff not_add_less1 power_0 to_nat_bound_to_length_bound)+
  have "(int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs)) mod n = (int (Nat_LSBF.to_nat ys) + (-1) mod n * int (Nat_LSBF.to_nat zs)) mod n"
    by (metis diff_minus_eq_add left_minus_one_mult_self mod_add_right_eq mod_mult_left_eq mult_minus1 power_one_right)
  also have "... = (int (Nat_LSBF.to_nat ys) + 2 ^ (2 ^ k) mod n * int (Nat_LSBF.to_nat zs)) mod n"
    using two_pow_half_carrier_length by simp
  also have "... = (int (Nat_LSBF.to_nat ys + 2 ^ (2 ^ k) * Nat_LSBF.to_nat zs)) mod n"
    by auto
  also have "... = (int (Nat_LSBF.to_nat (ys @ zs))) mod n"
    using \<open>length ys = 2 ^ k\<close> to_nat_app by presburger
  also have "... = (int (Nat_LSBF.to_nat xs)) mod n"
    using \<open>split xs = (ys, zs)\<close> app_split by presburger
  finally have 0: "(int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs)) mod n = (int (Nat_LSBF.to_nat xs)) mod n" .
  have "Nat_LSBF.to_nat (reduce xs) < n \<and> Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n \<and> length (reduce xs) \<le> 2 ^ k + 2"
  proof (cases "compare_nat zs ys")
    case True
    then have "reduce xs = subtract_nat ys zs"
      unfolding reduce_def \<open>split xs = (ys, zs)\<close> by simp
    then have 1: "Nat_LSBF.to_nat (reduce xs) = Nat_LSBF.to_nat ys - Nat_LSBF.to_nat zs"
      using subtract_nat_correct by presburger
    from True have "Nat_LSBF.to_nat zs \<le> Nat_LSBF.to_nat ys"
      using compare_nat_correct by blast
    with 1 have "int (Nat_LSBF.to_nat (reduce xs)) = int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs)"
      by linarith
    then have "int (Nat_LSBF.to_nat (reduce xs)) mod n = (int (Nat_LSBF.to_nat xs)) mod n"
      using 0 by presburger
    then have "Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n"
      using zmod_int by (metis of_nat_eq_iff)

    have "Nat_LSBF.to_nat (reduce xs) \<le> Nat_LSBF.to_nat ys" using 1 by linarith
    also have "... < n" using \<open>Nat_LSBF.to_nat ys < n\<close> .
    finally have "Nat_LSBF.to_nat (reduce xs) < n \<and> Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n"
      using \<open>Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n\<close> by blast
    moreover have "length (reduce xs) \<le> 2 ^ k + 2" unfolding \<open>reduce xs = subtract_nat ys zs\<close>
      apply (estimation estimate: conjunct2[OF subtract_nat_aux])
      using \<open>length zs = 2 ^ k\<close> \<open>length ys = 2 ^ k\<close> by simp
    ultimately show ?thesis by simp
  next
    case False
    then have reduce_eq: "reduce xs = subtract_nat (add_nat (True # replicate (2 ^ k - 1) False @ [True]) ys) zs"
      unfolding reduce_def \<open>split xs = (ys, zs)\<close> by simp
    then have "Nat_LSBF.to_nat (reduce xs) = 1 + 2 * (2 ^ (2 ^ k - 1)) + Nat_LSBF.to_nat ys - Nat_LSBF.to_nat zs"
      by (simp add: subtract_nat_correct add_nat_correct to_nat_app)
    also have "(1::nat) + 2 * (2 ^ (2 ^ k - 1)) = 1 + 2 ^ (2 ^ k - 1 + 1)"
      by (metis add.commute power_add power_one_right)
    also have "... = n"
      by simp
    finally have 1: "Nat_LSBF.to_nat (reduce xs) = n + Nat_LSBF.to_nat ys - Nat_LSBF.to_nat zs" .
    then have "Nat_LSBF.to_nat (reduce xs) < n"
      using False \<open>Nat_LSBF.to_nat ys < n\<close> \<open>Nat_LSBF.to_nat zs < n\<close> unfolding compare_nat_correct
      by linarith
    from 1 have "int (Nat_LSBF.to_nat (reduce xs)) = int n + int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs)"
      using \<open>Nat_LSBF.to_nat zs < n\<close> by linarith
    also have "... mod n = ((int n) mod n + (int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs))) mod n"
      using add_diff_eq
      using mod_add_left_eq[of "int n" "int n" "int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs)", symmetric]
      by metis
    also have "... = (int (Nat_LSBF.to_nat ys) - int (Nat_LSBF.to_nat zs)) mod n"
      using mod_self[of "int n"]
      by simp
    finally have "int (Nat_LSBF.to_nat (reduce xs)) mod n = int (Nat_LSBF.to_nat xs) mod n" using 0 by presburger
    then have "Nat_LSBF.to_nat (reduce xs) < n \<and> Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n"
      using \<open>Nat_LSBF.to_nat (reduce xs) < n\<close> zmod_int nat_int_comparison(1) by presburger
    moreover have "length (reduce xs) \<le> 2 ^ k + 2"
      unfolding reduce_eq
      apply (estimation estimate: conjunct2[OF subtract_nat_aux])
      apply (estimation estimate: length_add_nat_upper)
      unfolding \<open>length ys = 2 ^ k\<close> \<open>length zs = 2 ^ k\<close> by simp
    ultimately show ?thesis by simp
  qed
  then show "Nat_LSBF.to_nat (reduce xs) < n \<and> Nat_LSBF.to_nat (reduce xs) mod n = Nat_LSBF.to_nat xs mod n" "length (reduce xs) \<le> 2 ^ k + 2"
    by simp_all
qed

lemma reduce_correct:
  assumes "xs \<in> fermat_non_unique_carrier"
  shows "Nat_LSBF.to_nat xs mod n = Nat_LSBF.to_nat (reduce xs)"
  using reduce_correct'[OF assms] mod_less by metis

lemma add_take_drop_carry_aux:
  assumes "xs' = add_nat (take e xs) (drop e xs)"
  assumes "length xs = e + 1"
  assumes "e \<ge> 1"
  shows "length xs' \<le> e \<or> (xs' = replicate e False @ [True] \<and> xs = replicate e True @ [True])"
proof (intro verit_and_neg(3))
  assume a: "\<not> (length xs' \<le> e)"
  then have "length xs' \<ge> e + 1" by simp
  moreover have "length xs' \<le> e + 1"
    unfolding assms(1)
    apply (estimation estimate: length_add_nat_upper)
    using assms by simp
  ultimately have len_xs': "length xs' = e + 1" by simp
  moreover have "max (length (take e xs)) (length (drop e xs)) = e"
    using assms by simp
  ultimately have "\<exists>zs. xs' = zs @ [True]"
    unfolding assms(1) by (intro add_nat_last_bit_True, argo)
  then obtain zs where zs_def: "xs' = zs @ [True]" and len_zs: "length zs = e" using len_xs' by auto

  have "Nat_LSBF.to_nat xs' = Nat_LSBF.to_nat xs mod 2 ^ e + Nat_LSBF.to_nat xs div 2 ^ e"
    unfolding assms(1) by (simp add: add_nat_correct to_nat_take to_nat_drop)
  also have "... < (2 ^ e - 1) + (2 ^ (e + 1)) div 2 ^ e"
    apply (intro add_le_less_mono)
    subgoal using pos_mod_bound[of "2 ^ e" "Nat_LSBF.to_nat xs", OF two_pow_pos]
      by linarith
    subgoal using to_nat_length_upper_bound[of xs] assms div_le_mono
      by (metis add_diff_cancel_left' le_add1 less_mult_imp_div_less power_add power_commutes power_diff power_one_right to_nat_length_bound zero_neq_numeral)
    done
  also have "... = 2 ^ e + 1" by simp
  finally have "Nat_LSBF.to_nat xs' \<le> 2 ^ e" by simp
  moreover have "Nat_LSBF.to_nat xs' = Nat_LSBF.to_nat zs + 2 ^ e"
    unfolding zs_def by (simp add: to_nat_app len_zs)
  ultimately have "Nat_LSBF.to_nat zs = 0" by simp
  then have "zs = replicate e False" "Nat_LSBF.to_nat xs' = 2 ^ e"
    using len_zs to_nat_zero_iff truncate_Nil_iff \<open>Nat_LSBF.to_nat xs' = Nat_LSBF.to_nat zs + 2 ^ e\<close>
    by auto
  then have "xs' = replicate e False @ [True]" using zs_def by simp
  from assms(2) obtain xst xsh where xs_decomp: "xs = xst @ [xsh]" "length xst = e"
    by (metis Suc_eq_plus1 length_Suc_conv_rev)
  then have "take e xs = xst" "drop e xs = [xsh]" using assms by simp_all
  moreover have[simp]: "xsh = True"
  proof (rule ccontr)
    assume "xsh \<noteq> True"
    then have "drop e xs = [False]" using xs_decomp by simp
    then have "Nat_LSBF.to_nat xs' = Nat_LSBF.to_nat (take e xs)"
      unfolding assms(1) add_nat_correct by simp
    also have "... < 2 ^ e"
      using assms(2) to_nat_length_bound[of "take e xs"] by simp
    finally show False using \<open>Nat_LSBF.to_nat xs' = 2 ^ e\<close> by simp
  qed
  ultimately have "Nat_LSBF.to_nat xs' = Nat_LSBF.to_nat xst + 1" unfolding assms(1) add_nat_correct
    by simp
  then have "Nat_LSBF.to_nat xst = 2 ^ e - 1" using \<open>Nat_LSBF.to_nat xs' = 2 ^ e\<close> by simp
  then have "xst = replicate e True" using to_nat_replicate_True2[of xst] \<open>length xst = e\<close> by argo
  then have "xs = replicate e True @ [True]"
    using \<open>xs = xst @ [xsh]\<close> by simp
  then show "xs' = replicate e False @ [True] \<and> xs = replicate e True @ [True]"
    using \<open>xs' = replicate e False @ [True]\<close>
    by (simp add: replicate_append_same)
qed

function from_nat_lsbf :: "nat_lsbf \<Rightarrow> nat_lsbf" where
"from_nat_lsbf xs = (if length xs \<le> 2 ^ (k + 1) then fill (2 ^ (k + 1)) xs
    else from_nat_lsbf (add_nat (take (2 ^ (k + 1)) xs) (drop (2 ^ (k + 1)) xs)))"
  by pat_completeness auto
lemma from_nat_lsbf_dom_termination: "All from_nat_lsbf_dom"
proof (relation "measures [length, Nat_LSBF.to_nat]")
  show "wf (measures [length, Nat_LSBF.to_nat])" by simp
  fix xs :: nat_lsbf
  define e :: nat where "e = 2 ^ (k + 1)"
  then have e_ge_1: "e \<ge> 1" and e_ge_2: "e \<ge> 2" by simp_all
  define xs' where "xs' = add_nat (take e xs) (drop e xs)"
  assume "\<not> length xs \<le> 2 ^ (k + 1)"
  then have a: "length xs \<ge> e + 1" unfolding e_def by simp
  then consider "length xs = e + 1 \<and> length xs' \<le> e" |
      "length xs = e + 1 \<and> length xs' \<ge> e + 1" |
      "length xs \<ge> e + 2"
    by linarith
  then show "(add_nat (take (2 ^ (k + 1)) xs) (drop (2 ^ (k + 1)) xs), xs)
          \<in> measures [length, Nat_LSBF.to_nat]"
    unfolding e_def[symmetric] xs'_def[symmetric]
  proof cases
    case 1
    then show "(xs', xs) \<in> measures [length, Nat_LSBF.to_nat]" by simp
  next
    case 2
    with add_take_drop_carry_aux[OF xs'_def _ e_ge_1] have
      xs'_rep: "xs' = replicate e False @ [True]" and
      xs_rep: "xs = replicate e True @ [True]"
      by simp_all
    then have "Nat_LSBF.to_nat xs' < Nat_LSBF.to_nat xs \<longleftrightarrow> (0::nat) < 2 ^ e - 1"
      by (auto simp: to_nat_app)
    also have "..." using e_ge_1
      by (metis One_nat_def Suc_le_lessD less_2_cases_iff one_less_power zero_less_diff)
    finally show "(xs', xs) \<in> measures [length, Nat_LSBF.to_nat]"
      using 2 xs'_rep by simp
  next
    case 3
    have "length xs' \<le> max e (length xs - e) + 1"
      unfolding xs'_def
      apply (estimation estimate: length_add_nat_upper)
      by simp
    also have "... < length xs" using 3 e_ge_2 by simp
    finally show "(xs', xs) \<in> measures [length, Nat_LSBF.to_nat]" by simp
  qed
qed
termination by (rule from_nat_lsbf_dom_termination)

declare from_nat_lsbf.simps[simp del]

lemma from_nat_lsbf_correct:
  shows "from_nat_lsbf xs \<in> fermat_non_unique_carrier"
    "to_residue_ring (from_nat_lsbf xs) = to_residue_ring xs"
proof (induction xs rule: from_nat_lsbf.induct)
  case (1 xs)
  then show "from_nat_lsbf xs \<in> fermat_non_unique_carrier"
    apply (cases "length xs \<le> 2 ^ (k + 1)")
    subgoal
      unfolding fermat_non_unique_carrier_def
      by (simp add: from_nat_lsbf.simps[of xs] length_fill)
    subgoal
      by (simp add: from_nat_lsbf.simps[of xs])
    done
  show "to_residue_ring (from_nat_lsbf xs) = to_residue_ring xs"
  proof (cases "length xs \<le> 2 ^ (k + 1)")
    case True
    then show ?thesis
      by (simp add: from_nat_lsbf.simps[of xs])
  next
    case False
    let ?xs1 = "take (2 ^ (k + 1)) xs"
    let ?xs2 = "drop (2 ^ (k + 1)) xs"
    from False have "xs = ?xs1 @ ?xs2" by simp
    from False have "from_nat_lsbf xs = from_nat_lsbf (add_nat ?xs1 ?xs2)"
      by (simp add: from_nat_lsbf.simps[of xs])
    then have "to_residue_ring (from_nat_lsbf xs) = to_residue_ring (add_nat ?xs1 ?xs2)"
      using 1[OF False] by argo
    also have "... = (Nat_LSBF.to_nat ?xs1 + Nat_LSBF.to_nat ?xs2) mod n" by (simp add: add_nat_correct zmod_int)
    also have "... = (Nat_LSBF.to_nat ?xs1 + (2 ^ (2 ^ (k + 1))) * Nat_LSBF.to_nat ?xs2) mod n"
      using two_pow_carrier_length mod_add_right_eq mod_mult_left_eq
      by (metis (no_types, opaque_lifting) mult_numeral_1 numerals(1))
    also have "... = (Nat_LSBF.to_nat xs) mod n"
      by (intro_cong "[cong_tag_1 int, cong_tag_2 (mod)]" more: refl to_nat_drop_take[symmetric])
    finally show ?thesis by (simp add: zmod_int)
  qed
qed

lemma length_from_nat_lsbf: "length (from_nat_lsbf xs) = 2 ^ (k + 1)"
  using fermat_carrier_length[OF from_nat_lsbf_correct(1)] .

subsection "Implementing FNTT in $\\mathbb{Z}_{F_n}$"

lemma n_odd: "odd n"
  by simp

lemma ord_2: "ord n 2 = 2 ^ (k + 1)"
proof -
  have "ord n 2 dvd 2 ^ (k + 1)"
    using ord_divides[of "2::nat" "2 ^ (k + 1)" n]
    using two_pow_carrier_length
    by (simp add: cong_def)
  then obtain i where "ord n 2 = 2 ^ i" "i \<le> k + 1"
    using divides_primepow_nat[OF two_is_prime_nat]
    by blast
  have "i = k + 1"
  proof (rule ccontr)
    assume "i \<noteq> k + 1"
    then have "i \<le> k" using \<open>i \<le> k + 1\<close> by linarith
    have "1 \<noteq> (2::nat) ^ (2 ^ k) mod n" using two_pow_half_carrier_length_neq_1[symmetric] .
    moreover have "(2::nat) ^ (2 ^ k) mod n = 1"
    proof -
      have "(2::nat) ^ (2 ^ k) mod n = (2 ^ (2 ^ i)) ^ (2 ^ (k - i)) mod n"
        by (simp add: \<open>i \<le> k\<close> power_add[symmetric] power_mult[symmetric])
      also have "... = (2 ^ (2 ^ i) mod n) ^ (2 ^ (k - i)) mod n"
        by (simp add: power_mod)
      also have "2 ^ (2 ^ i) mod n = 1" using \<open>ord n 2 = 2 ^ i\<close>
        using ord[of 2 n] unfolding cong_def using n_gt_1 by simp
      finally show ?thesis by simp
    qed
    ultimately show "False" by argo
  qed
  then show ?thesis using \<open>ord n 2 = 2 ^ i\<close> by argo
qed
corollary ord_2_int: "ord (int n) 2 = 2 ^ (k + 1)"
  using ord_2 ord_int[of n 2] by simp

lemma two_is_primitive_root: "primitive_root (2 ^ (k + 1)) 2"
  apply (intro primitive_rootI)
  subgoal
    using two_in_carrier .
  subgoal
    using two_pow_carrier_length_residue_ring .
  subgoal for i
    using ord_2_int unfolding ord_def
    using pow_nat_eq not_less_Least cong_def
    by (metis (no_types, lifting) less_nat_zero_code one_cong)
  done

lemma two_inv_is_primitive_root: "primitive_root (2 ^ (k + 1)) (inv\<^bsub>Fn\<^esub> 2)"
  using primitive_root_inv[OF _ two_is_primitive_root] by simp

lemma two_powers_primitive_root:
  assumes "i + s = k + 1"
  assumes "i \<le> k"
  shows "primitive_root (2 ^ s) (2 [^]\<^bsub>Fn\<^esub> (2::nat) ^ i)"
proof (intro primitive_rootI nat_pow_closed two_in_carrier)

  have "(2 [^]\<^bsub>Fn\<^esub> (2::nat) ^ i) [^]\<^bsub>Fn\<^esub> (2::nat) ^ s = 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ (i + s))"
    by (simp add: nat_pow_pow[OF two_in_carrier] power_add)
  also have "... = \<one>\<^bsub>Fn\<^esub>"
    unfolding assms(1) by (rule two_pow_carrier_length_residue_ring)
  finally show "(2 [^]\<^bsub>Fn\<^esub> (2::nat) ^ i) [^]\<^bsub>Fn\<^esub> (2::nat) ^ s = \<one>\<^bsub>Fn\<^esub>" .

  fix j :: nat
  assume "0 < j" "j < 2 ^ s"
  then have "2 ^ i * j < 2 ^ (k + 1)"
    using power_add assms(1)
    by (metis nat_mult_less_cancel1 pos2 zero_less_power)
  have "2 ^ i * j > 0" using \<open>j > 0\<close> by simp
  have 1: "(\<forall>l\<in>{1..<(2::nat) ^ (k + 1)}. 2 [^]\<^bsub>Fn\<^esub> l \<noteq> \<one>\<^bsub>Fn\<^esub>)"
    using two_is_primitive_root unfolding primitive_root_def by simp
  have "(2 [^]\<^bsub>Fn\<^esub> (2::nat) ^ i) [^]\<^bsub>Fn\<^esub> j = 2 [^]\<^bsub>Fn\<^esub> (2 ^ i * j)"
    by (simp add: nat_pow_pow[OF two_in_carrier])
  also have "... \<noteq> \<one>\<^bsub>Fn\<^esub>"
    using 1 \<open>2 ^ i * j > 0\<close> \<open>2 ^ i * j < 2 ^ (k + 1)\<close> by simp
  finally show "(2 [^]\<^bsub>Fn\<^esub> (2::nat) ^ i) [^]\<^bsub>Fn\<^esub> j \<noteq> \<one>\<^bsub>Fn\<^esub>" .
qed

fun fft_combine_b_c_aux :: "(nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf) \<Rightarrow> (nat_lsbf \<Rightarrow> nat \<Rightarrow> nat_lsbf) \<Rightarrow> nat \<Rightarrow> nat_lsbf list \<times> nat \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list" where
"fft_combine_b_c_aux f g l (revs, e) [] [] = rev revs"
| "fft_combine_b_c_aux f g l (revs, e) (b # bs) (c # cs) =
    fft_combine_b_c_aux f g l ((f b (g c e)) # revs, (e + l) mod 2 ^ (k + 1)) bs cs"
| "fft_combine_b_c_aux f g l _ _ _ = undefined"

fun fft_ifft_combine_b_c_add where
"fft_ifft_combine_b_c_add True l bs cs = fft_combine_b_c_aux add_fermat divide_by_power_of_2 l ([], 0) bs cs"
| "fft_ifft_combine_b_c_add False l bs cs = fft_combine_b_c_aux add_fermat multiply_with_power_of_2 l ([], 0) bs cs"

fun fft_ifft_combine_b_c_subtract where
"fft_ifft_combine_b_c_subtract True l bs cs = fft_combine_b_c_aux subtract_fermat divide_by_power_of_2 l ([], 0) bs cs"
| "fft_ifft_combine_b_c_subtract False l bs cs = fft_combine_b_c_aux subtract_fermat multiply_with_power_of_2 l ([], 0) bs cs"

lemma fft_combine_b_c_aux_correct:
  assumes "length bs = len_bc" "length cs = len_bc"
  assumes "e < 2 ^ (k + 1)"
  shows "fft_combine_b_c_aux f g l (revs, e) bs cs = rev revs @ map3 (\<lambda>x y i. f x (g y ((e + l * i) mod 2 ^ (k + 1)))) bs cs [0..<len_bc]"
using assms proof (induction len_bc arbitrary: bs cs revs e)
  case 0
  then have "bs = []" "cs = []" by simp_all
  then show ?case by simp
next
  case (Suc len_bc)
  then obtain b bs' c cs' where bcs: "bs = b # bs'" "cs = c # cs'" by (meson length_Suc_conv)
  with Suc.prems have len_bcs': "length bs' = len_bc" "length cs' = len_bc" by simp_all
  have "(e + l * i) mod 2 ^ (k + 1) < 2 ^ (k + 1)" for i by simp
  note ih = Suc.IH[OF len_bcs' this]
  have "fft_combine_b_c_aux f g l (revs, e) bs cs =
    fft_combine_b_c_aux f g l (f b (g c e) # revs, (e + l) mod (2 * 2 ^ k)) bs' cs'"
    unfolding bcs by simp
  also have "... = rev (f b (g c e) # revs) @
    map3 (\<lambda>x y i. f x (g y (((e + l * 1) mod 2 ^ (k + 1) + l * i) mod 2 ^ (k + 1)))) bs' cs'
    [0..<len_bc]"
    using ih[of "f b (g c e) # revs" 1] by simp
  also have "... = rev revs @ (f b (g c e) #
      map3 (\<lambda>x y i. f x (g y (((e + l * 1) mod 2 ^ (k + 1) + l * i) mod 2 ^ (k + 1)))) bs' cs'
      [0..<len_bc])"
    by simp
  finally have r: "fft_combine_b_c_aux f g l (revs, e) bs cs = ..." .
  show ?case unfolding r
  proof (intro arg_cong2[where f = "(@)"] refl)
    have "f b (g c e) #
      map3 (\<lambda>x y i. f x (g y (((e + l * 1) mod 2 ^ (k + 1) + l * i) mod 2 ^ (k + 1)))) bs' cs' [0..<len_bc] =
      f b (g c (e + l * 0)) #
      map3 (\<lambda>x y i. f x (g y ((e + l * Suc i) mod 2 ^ (k + 1)))) bs' cs' [0..<len_bc]"
      (is "?l = ?f # ?m3")
      apply (intro arg_cong2[where f = "(#)"])
      subgoal by simp
      subgoal
        unfolding append.append_Nil
        apply (intro arg_cong[where f = "\<lambda>i. map3 i _ _ _"])
        by (simp add: add.assoc mod_add_left_eq)
      done
    also have "?m3 = map3 (\<lambda>x y i. f x (g y ((e + l * i) mod 2 ^ (k + 1)))) bs' cs' (map Suc [0..<len_bc])"
      by (rule map3_compose3)
    also have "... = map3 (\<lambda>x y i. f x (g y ((e + l * i) mod 2 ^ (k + 1)))) bs' cs' [Suc 0..<Suc len_bc]"
      by (subst map_Suc_upt) (rule refl)
    also have "?f # ... = map3 (\<lambda>x y i. f x (g y ((e + l * i) mod 2 ^ (k + 1)))) bs cs [0..<Suc len_bc]"
      unfolding upt_conv_Cons[OF zero_less_Suc[of len_bc]] bcs using Suc.prems by simp
    finally show "?l = ..." .
  qed
qed

lemma fft_ifft_combine_b_c_add_correct:
  assumes "length bs = len_bc" "length cs = len_bc"
  shows "fft_ifft_combine_b_c_add it l bs cs = map3 (\<lambda>x y i. add_fermat x ((if it then divide_by_power_of_2 else multiply_with_power_of_2) y ((l * i) mod 2 ^ (k + 1)))) bs cs [0..<len_bc]"
  by (cases it; simp add: fft_combine_b_c_aux_correct[OF assms])

lemma fft_ifft_combine_b_c_subtract_correct:
  assumes "length bs = len_bc" "length cs = len_bc"
  shows "fft_ifft_combine_b_c_subtract it l bs cs = map3 (\<lambda>x y i. subtract_fermat x ((if it then divide_by_power_of_2 else multiply_with_power_of_2) y ((l * i) mod 2 ^ (k + 1)))) bs cs [0..<len_bc]"
  by (cases it; simp add: fft_combine_b_c_aux_correct[OF assms])

lemma fft_ifft_combine_b_c_add_carrier:
  assumes "length bs = len_bc" "length cs = len_bc"
  assumes "set bs \<subseteq> fermat_non_unique_carrier"
  assumes "set cs \<subseteq> fermat_non_unique_carrier"
  shows "set (fft_ifft_combine_b_c_add it l bs cs) \<subseteq> fermat_non_unique_carrier"
  unfolding fft_ifft_combine_b_c_add_correct[OF assms(1) assms(2)]
  apply (intro set_map3_subseteqI[OF _ assms(3) assms(4) subset_refl] add_fermat_closed)
   apply (simp_all add: divide_by_power_of_2_closed multiply_with_power_of_2_closed)
  done

lemma fft_ifft_combine_b_c_subtract_carrier:
  assumes "length bs = len_bc" "length cs = len_bc"
  assumes "set bs \<subseteq> fermat_non_unique_carrier"
  assumes "set cs \<subseteq> fermat_non_unique_carrier"
  shows "set (fft_ifft_combine_b_c_subtract it l bs cs) \<subseteq> fermat_non_unique_carrier"
  unfolding fft_ifft_combine_b_c_subtract_correct[OF assms(1) assms(2)]
  apply (intro set_map3_subseteqI[OF _ assms(3) assms(4) subset_refl] subtract_fermat_closed)
   apply (simp_all add: divide_by_power_of_2_closed multiply_with_power_of_2_closed)
  done

fun fft_ifft :: "bool \<Rightarrow> nat \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf list" where
"fft_ifft it l [] = []"
| "fft_ifft it l [x] = [x]"
| "fft_ifft it l [x, y] = [add_fermat x y, subtract_fermat x y]"
| "fft_ifft it l a = (let nums1 = evens_odds True a;
                  nums2 = evens_odds False a;
                  b = fft_ifft it (2 * l) nums1;
                  c = fft_ifft it (2 * l) nums2;
                  g = fft_ifft_combine_b_c_add it l b c;
                  h = fft_ifft_combine_b_c_subtract it l b c
                   in g@h)"

(* fft l xs performs the fast fourier transform of xs with primitive root of unity 2 ^ l *)
fun fft where "fft l xs = fft_ifft False l xs"
fun ifft where "ifft l xs = fft_ifft True l xs"

end

locale fft_context = int_lsbf_fermat +
  fixes it :: bool
  fixes l e :: nat
  fixes a1 a2 a3 :: nat_lsbf
  fixes as :: "nat_lsbf list"
  assumes length_a': "length (a1 # a2 # a3 # as) = 2 ^ e"
begin

definition a where "a = a1 # a2 # a3 # as"
definition nums1 where "nums1 = evens_odds True a"
definition nums2 where "nums2 = evens_odds False a"
definition b where "b = fft_ifft it (2 * l) nums1"
definition c where "c = fft_ifft it (2 * l) nums2"
definition g where "g = fft_ifft_combine_b_c_add it l b c"
definition h where "h = fft_ifft_combine_b_c_subtract it l b c"
lemmas defs = a_def nums1_def nums2_def b_def c_def g_def h_def

lemma length_a: "length a = 2 ^ e" unfolding a_def by (rule length_a')
lemma e_ge_2: "e \<ge> 2"
proof (rule ccontr)
  assume "\<not> e \<ge> 2"
  then have "e \<le> 1" by simp
  have "(2::nat) ^ e \<le> 2" using power_increasing[OF \<open>e \<le> 1\<close>, of "2::nat"] by simp
  then show False using length_a' by simp
qed
lemma e_pos: "e > 0" using e_ge_2 by simp
lemma two_pow_e_div_2: "(2::nat) ^ e div 2 = 2 ^ (e - 1)"
  using gr0_implies_Suc[OF e_pos] by auto
lemma two_pow_e_as_sum: "(2::nat) ^ e = 2 ^ (e - 1) + 2 ^ (e - 1)"
  by (metis e_pos two_pow_e_div_2 even_power even_two_times_div_two gcd_nat.eq_iff mult_2)

lemma
  shows length_nums1: "length nums1 = 2 ^ (e - 1)"
  and length_nums2: "length nums2 = 2 ^ (e - 1)"
  unfolding nums1_def nums2_def length_evens_odds length_a 
  using two_pow_e_div_2 by simp_all

lemma result_eq: "fft_ifft it l a = g @ h"
  unfolding a_def fft_ifft.simps[of it l] Let_def
  unfolding defs[symmetric] by (rule refl)

lemma
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows nums1_carrier: "set nums1 \<subseteq> fermat_non_unique_carrier"
  and nums2_carrier: "set nums2 \<subseteq> fermat_non_unique_carrier"
  unfolding nums1_def nums2_def atomize_conj
  by (intro conjI subset_trans[OF set_evens_odds] assms)

end

context int_lsbf_fermat
begin

lemma length_fft_ifft:
  assumes "length a = 2 ^ e"
  shows "length (fft_ifft it l a) = 2 ^ e"
  using assms
proof (induction it l a arbitrary: e rule: fft_ifft.induct)
  case (4 it l a1 a2 a3 as)
  interpret fft_context k it l e a1 a2 a3 as
    apply unfold_locales
    using 4 by argo

  have len_b: "length b = 2 ^ (e - 1)"
    unfolding b_def
    apply (intro "4.IH"[of nums1 nums2])
    unfolding defs[symmetric] length_nums1
    by (rule refl)+
  have len_c: "length c = 2 ^ (e - 1)"
    unfolding c_def
    apply (intro "4.IH"(2)[of nums1 nums2 b])
    unfolding defs[symmetric] length_nums2
    by (rule refl)+
  have len_g: "length g = 2 ^ (e - 1)"
    unfolding g_def fft_ifft_combine_b_c_add_correct[OF len_b len_c] map3_as_map
    by (simp add: len_b len_c)
  have len_h: "length h = 2 ^ (e - 1)"
    unfolding h_def fft_ifft_combine_b_c_subtract_correct[OF len_b len_c] map3_as_map
    by (simp add: len_b len_c)
  show ?case
    unfolding a_def[symmetric] result_eq
    by (simp add: len_g len_h e_pos two_pow_e_as_sum)
qed simp_all

lemma length_fft:
  assumes "length a = 2 ^ e"
  shows "length (fft l a) = 2 ^ e"
  unfolding fft.simps length_fft_ifft[OF assms] by (rule refl)

lemma length_ifft:
  assumes "length a = 2 ^ e"
  shows "length (ifft l a) = 2 ^ e"
  unfolding ifft.simps length_fft_ifft[OF assms] by (rule refl)

end

context fft_context begin

lemma length_b: "length b = 2 ^ (e - 1)"
  unfolding b_def by (intro length_fft_ifft length_nums1)
lemma length_c: "length c = 2 ^ (e - 1)"
  unfolding c_def by (intro length_fft_ifft length_nums2)
lemma length_g: "length g = 2 ^ (e - 1)"
  unfolding g_def fft_ifft_combine_b_c_add_correct[OF length_b length_c] map3_as_map
  by (simp add: length_b length_c)
lemma length_h: "length h = 2 ^ (e - 1)"
  unfolding h_def fft_ifft_combine_b_c_subtract_correct[OF length_b length_c] map3_as_map
  by (simp add: length_b length_c)

end

context int_lsbf_fermat
begin

lemma fft_ifft_carrier:
  assumes "length a = 2 ^ l"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "set (fft_ifft it s a) \<subseteq> fermat_non_unique_carrier"
using assms proof (induction it s a arbitrary: l rule: fft_ifft.induct)
  case (1 it s)
  then show ?case by simp
next
  case (2 it s x)
  then show ?case by simp
next
  case (3 it s x y)
  then show ?case by (simp add: add_fermat_closed subtract_fermat_closed)
next
  case (4 it s a1 a2 a3 as)
  interpret fft_context k it s l a1 a2 a3 as
    apply unfold_locales using 4 by simp

  have b_carrier: "set b \<subseteq> fermat_non_unique_carrier"
    unfolding b_def
    apply (intro "4.IH"(1)[of nums1 nums2 "l - 1"])
    unfolding defs[symmetric]
    using nums1_carrier length_nums1 "4.prems" a_def by simp_all
  have c_carrier: "set c \<subseteq> fermat_non_unique_carrier"
    unfolding c_def
    apply (intro "4.IH"(2)[of nums1 nums2 b "l - 1"])
    unfolding defs[symmetric]
    using nums2_carrier length_nums2 "4.prems" a_def by simp_all
    

  have g_carrier: "set g \<subseteq> fermat_non_unique_carrier"
    unfolding g_def
    apply (intro fft_ifft_combine_b_c_add_carrier)
    using length_b length_c b_carrier c_carrier by simp_all
  have h_carrier: "set h \<subseteq> fermat_non_unique_carrier"
    unfolding h_def
    apply (intro fft_ifft_combine_b_c_subtract_carrier)
    using length_b length_c b_carrier c_carrier by simp_all

  show ?case
    unfolding defs[symmetric] result_eq
    using g_carrier h_carrier by simp
qed

lemma fft_carrier:
  assumes "length a = 2 ^ l"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "set (fft s a) \<subseteq> fermat_non_unique_carrier"
  using fft_ifft_carrier[OF assms] by simp

lemma ifft_carrier:
  assumes "length a = 2 ^ l"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "set (ifft s a) \<subseteq> fermat_non_unique_carrier"
  using fft_ifft_carrier[OF assms] by simp

lemma fft_ifft_correct':
  assumes "length a = 2 ^ l"
  assumes "l \<le> k + 1"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "map to_residue_ring (fft_ifft it s a) = FNTT'' ((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s) (map to_residue_ring a)"
  using assms
proof (induction it s a arbitrary: l rule: fft_ifft.induct)
  case (1 it s)
  then show ?case by simp
next
  case (2 it s x)
  then show ?case by simp
next
  case (3 it s x y)
  then show ?case using add_fermat_correct subtract_fermat_correct by simp
next
  case (4 it s a1 a2 a3 as)
  interpret fft_context k it s l a1 a2 a3 as
    apply unfold_locales using 4 by simp

(* definitions of FNTT *)
  define nums1' where "nums1' = evens_odds True (map to_residue_ring local.a)"
  define nums2' where "nums2' = evens_odds False (map to_residue_ring local.a)"
  define b' where "b' = FNTT'' (((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> (2::nat)) nums1'"
  define c' where "c' = FNTT'' (((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> (2::nat)) nums2'"
  define g' where "g' = map2 (\<oplus>\<^bsub>Fn\<^esub>) b'
              (map2 (\<otimes>\<^bsub>Fn\<^esub>)
                (map (([^]\<^bsub>Fn\<^esub>) ((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) c')"
  define h' where "h' = map2 (a_minus Fn) b'
              (map2 (\<otimes>\<^bsub>Fn\<^esub>)
                (map (([^]\<^bsub>Fn\<^esub>) ((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) c')"
  note defs' = a_def nums1'_def nums2'_def b'_def c'_def g'_def h'_def

  have fntt_def: "FNTT'' ((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s) (map to_residue_ring (a1 # a2 # a3 # as))
    = g' @ h'"
    using length_map[of to_residue_ring local.a]
    by (simp only: list.map(2) FNTT''.simps Let_def defs')

(* correspondences *)
  from two_is_primitive_root have "root_of_unity (2 ^ (k + 1)) 2"
    unfolding primitive_root_def by blast

  from e_ge_2 have "Suc (k + 1 - l) \<le> k" using \<open>l \<le> k + 1\<close> by linarith

  have pr_unit: "(if it then inv\<^bsub>Fn\<^esub> 2 else 2) \<in> Units Fn"
    using two_is_unit Units_inv_Units by algebra
  then have pr_carrier: "(if it then inv\<^bsub>Fn\<^esub> 2 else 2) \<in> carrier Fn"
    by (rule Units_closed)
  have pow_2s: "((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> (2::nat) = (if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> (2 * s)"
    using nat_pow_pow[OF pr_carrier, of s 2] mult.commute[of s 2] by argo

  from e_ge_2 obtain l' where l'_def[simp]: "l = Suc l'"
    by (metis not_numeral_le_zero old.nat.exhaust)

  have l'_le: "l' \<le> k + 1"
    using \<open>l \<le> k + 1\<close> \<open>l = Suc l'\<close> by linarith

  have nums1'_def': "nums1' = map to_residue_ring nums1"
    by (simp add: nums1'_def nums1_def map_evens_odds)
  then have length_nums1': "length nums1' = 2 ^ l'" using length_nums1 \<open>l = Suc l'\<close> by simp
  have nums2'_def': "nums2' = map to_residue_ring nums2"
    by (simp add: nums2'_def nums2_def map_evens_odds)
  then have length_nums2': "length nums2' = 2 ^ l'" using length_nums2 \<open>l = Suc l'\<close> by simp

  have "set local.a \<subseteq> fermat_non_unique_carrier" using 4 by (simp only: a_def)
  have nums1_carrier: "set nums1 \<subseteq> fermat_non_unique_carrier"
    unfolding nums1_def using \<open>set local.a \<subseteq> fermat_non_unique_carrier\<close> set_evens_odds by fastforce

  have b_b': "b' = map to_residue_ring b"
    unfolding b'_def b_def nums1'_def map_evens_odds[symmetric] pow_2s nums1_def
    apply (intro 4(1)[symmetric, of _ nums2 l'])
    subgoal unfolding a_def by (rule refl)
    subgoal unfolding nums2_def a_def by (rule refl)
    subgoal unfolding defs[symmetric] length_nums1 by simp
    subgoal by (rule l'_le)
    subgoal unfolding defs[symmetric] by (rule nums1_carrier)
    done
  then have length_b': "length b' = 2 ^ l'"
    using length_b by simp

  have nums2_carrier: "set nums2 \<subseteq> fermat_non_unique_carrier"
    unfolding nums2_def using \<open>set local.a \<subseteq> fermat_non_unique_carrier\<close> set_evens_odds by fastforce

  have c_c': "c' = map to_residue_ring c"
    unfolding c'_def c_def nums2'_def map_evens_odds[symmetric] pow_2s nums2_def
    apply (intro 4(2)[symmetric, of nums1 _ b l'])
    subgoal unfolding defs by (rule refl)
    subgoal unfolding a_def by (rule refl)
    subgoal unfolding defs[symmetric] by (rule refl)
    subgoal unfolding defs[symmetric] length_nums2 by simp
    subgoal by (rule l'_le)
    subgoal unfolding defs[symmetric] by (rule nums2_carrier)
    done
  then have length_c': "length c' = 2 ^ l'"
    using length_c by simp
  
  have b_carrier: "set b \<subseteq> fermat_non_unique_carrier"
    unfolding b_def
    apply (intro fft_ifft_carrier nums1_carrier) using length_nums1 by simp
  have c_carrier: "set c \<subseteq> fermat_non_unique_carrier"
    unfolding c_def
    apply (intro fft_ifft_carrier nums2_carrier) using length_nums2 by simp

  have length_nums1': "length nums1' = 2 ^ l'"
    using length_nums1 nums1'_def' by simp
  have length_nums2': "length nums2' = 2 ^ l'"
    using length_nums2 nums2'_def' by simp

  have length_g': "length g' = 2 ^ l'"
    unfolding g'_def by (simp add: length_a length_b' length_c')
  have length_h': "length h' = 2 ^ l'"
    unfolding h'_def by (simp add: length_a length_b' length_c')

  have g_g': "g' = map to_residue_ring g"
  proof (intro nth_equalityI)
    show "length g' = length (map to_residue_ring g)"
      by (simp add: length_g length_g')
  next
    fix i
    assume "i < length g'"
    then have i_less: "i < 2 ^ (l - 1)" unfolding length_g' using \<open>l = Suc l'\<close> by simp

    have bi_carrier: "b ! i \<in> fermat_non_unique_carrier"
      using set_subseteqD[OF b_carrier] length_b i_less by simp
    have ci_carrier: "c ! i \<in> fermat_non_unique_carrier"
      using set_subseteqD[OF c_carrier] length_c i_less by simp

    have bi_b'i: "to_residue_ring (b ! i) = b' ! i"
      unfolding b_b' by (intro nth_map[symmetric]; simp add: length_b i_less del: \<open>l = Suc l'\<close> One_nat_def)
    have ci_c'i: "to_residue_ring (c ! i) = c' ! i"
      unfolding c_c' by (intro nth_map[symmetric]; simp add: length_c i_less del: \<open>l = Suc l'\<close> One_nat_def)
    
    show "g' ! i = (map to_residue_ring g) ! i"
    proof (cases it)
      case True
      then have it_op: "(if it then divide_by_power_of_2 else multiply_with_power_of_2) = divide_by_power_of_2" by argo
      have "map to_residue_ring g ! i = to_residue_ring (g ! i)"
        apply (intro nth_map)
        unfolding length_g using i_less by simp
      also have "... = to_residue_ring (add_fermat (b ! i) (divide_by_power_of_2 (c ! i) (s * ([0..<2 ^ (l - 1)] ! i) mod 2 ^ (k + 1))))"
        unfolding g_def fft_ifft_combine_b_c_add_correct[OF length_b length_c] it_op
        apply (intro arg_cong[where f = to_residue_ring] nth_map3)
        unfolding length_b length_c using i_less by simp_all
      also have "... = to_residue_ring (add_fermat (b ! i) (divide_by_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1))))"
        using i_less by simp
      also have "... = to_residue_ring (b ! i) \<oplus>\<^bsub>Fn\<^esub> to_residue_ring (divide_by_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1)))"
        by (intro add_fermat_correct bi_carrier divide_by_power_of_2_closed ci_carrier)
      also have "... = to_residue_ring (b ! i) \<oplus>\<^bsub>Fn\<^esub> to_residue_ring (c ! i) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        by (intro arg_cong2[where f = "(\<oplus>\<^bsub>Fn\<^esub>)"] divide_by_power_of_2_correct refl ci_carrier)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        unfolding bi_b'i ci_c'i by (rule refl)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i)"
        by (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fn\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: inv_pow_mod_carrier_length mod_mod_trivial)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> ((inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i)"
        by (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fn\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: nat_pow_pow[symmetric] Units_inv_closed two_is_unit)
      finally have 1: "map to_residue_ring g ! i = ..." .
      have "g' ! i = map3 (\<lambda>x y z. x \<oplus>\<^bsub>Fn\<^esub> y \<otimes>\<^bsub>Fn\<^esub> z) b' (map (([^]\<^bsub>Fn\<^esub>) (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) c' ! i"
        unfolding g'_def eqTrueI[OF True] if_True map2_of_map2_r by (rule refl)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> ((map (([^]\<^bsub>Fn\<^esub>) (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) ! i) \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        using i_less length_b' length_c' \<open>l = Suc l'\<close> length_a by (intro nth_map3) simp_all
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fn\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]")
        using nth_map length_a \<open>l = Suc l'\<close> i_less by simp
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i"
        apply (intro arg_cong2[where f = "(\<oplus>\<^bsub>Fn\<^esub>)"] refl m_comm nat_pow_closed Units_inv_closed two_is_unit)
        using to_residue_ring_in_carrier ci_c'i[symmetric] by simp
      finally show ?thesis unfolding 1 .
    next
      case False
      then have it_op: "(if it then divide_by_power_of_2 else multiply_with_power_of_2) = multiply_with_power_of_2" by argo
      have "map to_residue_ring g ! i = to_residue_ring (g ! i)"
        apply (intro nth_map)
        unfolding length_g using i_less by simp
      also have "... = to_residue_ring (add_fermat (b ! i) (multiply_with_power_of_2 (c ! i) (s * ([0..<2 ^ (l - 1)] ! i) mod 2 ^ (k + 1))))"
        unfolding g_def fft_ifft_combine_b_c_add_correct[OF length_b length_c] it_op
        apply (intro arg_cong[where f = to_residue_ring] nth_map3)
        unfolding length_b length_c using i_less by simp_all
      also have "... = to_residue_ring (add_fermat (b ! i) (multiply_with_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1))))"
        using i_less by simp
      also have "... = to_residue_ring (b ! i) \<oplus>\<^bsub>Fn\<^esub> to_residue_ring (multiply_with_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1)))"
        by (intro add_fermat_correct bi_carrier multiply_with_power_of_2_closed ci_carrier)
      also have "... = to_residue_ring (b ! i) \<oplus>\<^bsub>Fn\<^esub> to_residue_ring (c ! i) \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        by (intro arg_cong2[where f = "(\<oplus>\<^bsub>Fn\<^esub>)"] multiply_with_power_of_2_correct refl ci_carrier)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        unfolding bi_b'i ci_c'i by (rule refl)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i)"
        by (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fn\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: pow_mod_carrier_length mod_mod_trivial)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> ((2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i)"
        by (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fn\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: nat_pow_pow[symmetric] two_in_carrier)
      finally have 1: "map to_residue_ring g ! i = ..." .
      have "g' ! i = map3 (\<lambda>x y z. x \<oplus>\<^bsub>Fn\<^esub> y \<otimes>\<^bsub>Fn\<^esub> z) b' (map (([^]\<^bsub>Fn\<^esub>) (2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) c' ! i"
        unfolding g'_def if_False map2_of_map2_r by (simp add: False)
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> ((map (([^]\<^bsub>Fn\<^esub>) (2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) ! i) \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        using i_less length_b' length_c' \<open>l = Suc l'\<close> length_a by (intro nth_map3) simp_all
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fn\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]")
        using nth_map length_a \<open>l = Suc l'\<close> i_less by simp
      also have "... = (b' ! i) \<oplus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i"
        apply (intro arg_cong2[where f = "(\<oplus>\<^bsub>Fn\<^esub>)"] refl m_comm nat_pow_closed two_in_carrier)
        using to_residue_ring_in_carrier ci_c'i[symmetric] by simp
      finally show ?thesis unfolding 1 .
    qed
  qed

  have h_h': "h' = map to_residue_ring h"
  proof (intro nth_equalityI)
    show "length h' = length (map to_residue_ring h)"
      by (simp add: length_h length_h')
  next
    fix i
    assume "i < length h'"
    then have i_less: "i < 2 ^ (l - 1)" unfolding length_h' using \<open>l = Suc l'\<close> by simp

    have bi_carrier: "b ! i \<in> fermat_non_unique_carrier"
      using set_subseteqD[OF b_carrier] length_b i_less by simp
    have ci_carrier: "c ! i \<in> fermat_non_unique_carrier"
      using set_subseteqD[OF c_carrier] length_c i_less by simp

    have bi_b'i: "to_residue_ring (b ! i) = b' ! i"
      unfolding b_b' by (intro nth_map[symmetric]; simp add: length_b i_less del: \<open>l = Suc l'\<close> One_nat_def)
    have ci_c'i: "to_residue_ring (c ! i) = c' ! i"
      unfolding c_c' by (intro nth_map[symmetric]; simp add: length_c i_less del: \<open>l = Suc l'\<close> One_nat_def)
    
    show "h' ! i = (map to_residue_ring h) ! i"
    proof (cases it)
      case True
      then have it_op: "(if it then divide_by_power_of_2 else multiply_with_power_of_2) = divide_by_power_of_2" by argo
      have "map to_residue_ring h ! i = to_residue_ring (h ! i)"
        apply (intro nth_map)
        unfolding length_h using i_less by simp
      also have "... = to_residue_ring (subtract_fermat (b ! i) (divide_by_power_of_2 (c ! i) (s * ([0..<2 ^ (l - 1)] ! i) mod 2 ^ (k + 1))))"
        unfolding h_def fft_ifft_combine_b_c_subtract_correct[OF length_b length_c] it_op
        apply (intro arg_cong[where f = to_residue_ring] nth_map3)
        unfolding length_b length_c using i_less by simp_all
      also have "... = to_residue_ring (subtract_fermat (b ! i) (divide_by_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1))))"
        using i_less by simp
      also have "... = to_residue_ring (b ! i) \<ominus>\<^bsub>Fn\<^esub> to_residue_ring (divide_by_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1)))"
        by (intro subtract_fermat_correct bi_carrier divide_by_power_of_2_closed ci_carrier)
      also have "... = to_residue_ring (b ! i) \<ominus>\<^bsub>Fn\<^esub> to_residue_ring (c ! i) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        by (intro arg_cong2[where f = "(\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y)"] divide_by_power_of_2_correct refl ci_carrier)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        unfolding bi_b'i ci_c'i by (rule refl)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i)"
        by (intro_cong "[cong_tag_2 (\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: inv_pow_mod_carrier_length mod_mod_trivial)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> ((inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i)"
        by (intro_cong "[cong_tag_2 (\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: nat_pow_pow[symmetric] Units_inv_closed two_is_unit)
      finally have 1: "map to_residue_ring h ! i = ..." .
      have "h' ! i = map3 (\<lambda>x y z. x \<ominus>\<^bsub>Fn\<^esub> y \<otimes>\<^bsub>Fn\<^esub> z) b' (map (([^]\<^bsub>Fn\<^esub>) (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) c' ! i"
        unfolding h'_def eqTrueI[OF True] if_True map2_of_map2_r by (rule refl)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> ((map (([^]\<^bsub>Fn\<^esub>) (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) ! i) \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        using i_less length_b' length_c' \<open>l = Suc l'\<close> length_a by (intro nth_map3) simp_all
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        apply (intro_cong "[cong_tag_2 (\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]")
        using nth_map length_a \<open>l = Suc l'\<close> i_less by simp
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i"
        apply (intro arg_cong2[where f = "(\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y)"] refl m_comm nat_pow_closed Units_inv_closed two_is_unit)
        using to_residue_ring_in_carrier ci_c'i[symmetric] by simp
      finally show ?thesis unfolding 1 .
    next
      case False
      then have it_op: "(if it then divide_by_power_of_2 else multiply_with_power_of_2) = multiply_with_power_of_2" by argo
      have "map to_residue_ring h ! i = to_residue_ring (h ! i)"
        apply (intro nth_map)
        unfolding length_h using i_less by simp
      also have "... = to_residue_ring (subtract_fermat (b ! i) (multiply_with_power_of_2 (c ! i) (s * ([0..<2 ^ (l - 1)] ! i) mod 2 ^ (k + 1))))"
        unfolding h_def fft_ifft_combine_b_c_subtract_correct[OF length_b length_c] it_op
        apply (intro arg_cong[where f = to_residue_ring] nth_map3)
        unfolding length_b length_c using i_less by simp_all
      also have "... = to_residue_ring (subtract_fermat (b ! i) (multiply_with_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1))))"
        using i_less by simp
      also have "... = to_residue_ring (b ! i) \<ominus>\<^bsub>Fn\<^esub> to_residue_ring (multiply_with_power_of_2 (c ! i) (s * i mod 2 ^ (k + 1)))"
        by (intro subtract_fermat_correct bi_carrier multiply_with_power_of_2_closed ci_carrier)
      also have "... = to_residue_ring (b ! i) \<ominus>\<^bsub>Fn\<^esub> to_residue_ring (c ! i) \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        by (intro arg_cong2[where f = "(\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y)"] multiply_with_power_of_2_correct refl ci_carrier)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i mod 2 ^ (k + 1))"
        unfolding bi_b'i ci_c'i by (rule refl)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (s * i)"
        by (intro_cong "[cong_tag_2 (\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: pow_mod_carrier_length mod_mod_trivial)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> ((2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i)"
        by (intro_cong "[cong_tag_2 (\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: nat_pow_pow[symmetric] two_in_carrier)
      finally have 1: "map to_residue_ring h ! i = ..." .
      have "h' ! i = map3 (\<lambda>x y z. x \<ominus>\<^bsub>Fn\<^esub> y \<otimes>\<^bsub>Fn\<^esub> z) b' (map (([^]\<^bsub>Fn\<^esub>) (2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) c' ! i"
        unfolding h'_def if_False map2_of_map2_r by (simp add: False)
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> ((map (([^]\<^bsub>Fn\<^esub>) (2 [^]\<^bsub>Fn\<^esub> s)) [0..<length local.a div 2]) ! i) \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        using i_less length_b' length_c' \<open>l = Suc l'\<close> length_a by (intro nth_map3) simp_all
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i \<otimes>\<^bsub>Fn\<^esub> (c' ! i)"
        apply (intro_cong "[cong_tag_2 (\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y), cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]")
        using nth_map length_a \<open>l = Suc l'\<close> i_less by simp
      also have "... = (b' ! i) \<ominus>\<^bsub>Fn\<^esub> (c' ! i) \<otimes>\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> i"
        apply (intro arg_cong2[where f = "(\<lambda>x y. x \<ominus>\<^bsub>Fn\<^esub> y)"] refl m_comm nat_pow_closed two_in_carrier)
        using to_residue_ring_in_carrier ci_c'i[symmetric] by simp
      finally show ?thesis unfolding 1 .
    qed
  qed
  show ?case
    using fntt_def
    unfolding a_def[symmetric] result_eq map_append g_g'[symmetric] h_h'[symmetric]
    by argo
qed

lemma fft_ifft_correct:
  assumes "length a = 2 ^ l"
  assumes "s = 2 ^ i"
  assumes "i + l = k + 1"
  assumes "l > 0"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "map to_residue_ring (fft_ifft it s a) = NTT ((if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s) (map to_residue_ring a)"
proof -
  let ?\<mu> = "(if it then inv\<^bsub>Fn\<^esub> 2 else 2) [^]\<^bsub>Fn\<^esub> s"
  have inv2s: "(inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> s) = inv\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s)"
    by (intro inv_nat_pow[symmetric] two_is_unit)

  then have it_unfold: "it \<Longrightarrow> ?\<mu> = inv\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> s)" "\<not> it \<Longrightarrow> ?\<mu> = 2 [^]\<^bsub>Fn\<^esub> s"
    by simp_all
  from assms have "l \<le> k + 1" by simp
  from assms have "i \<le> k" by simp
  then have "(2::nat) ^ i \<le> 2 ^ k" by simp

  have "2 ^ l div 2 = (2::nat) ^ (l - 1)" using \<open>l > 0\<close> by (simp add: Suc_leI power_diff)
  then have pow_2sl: "(2 [^]\<^bsub>Fn\<^esub> s) [^]\<^bsub>Fn\<^esub> ((2::nat) ^ l div 2) = \<ominus>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub>"
    using two_powers_half_carrier_length_residue_ring[of i "l - 1"]
    using \<open>l > 0\<close> \<open>i + l = k + 1\<close> \<open>s = 2 ^ i\<close> two_powers_trivial[of "2 ^ i"] \<open>i \<le> k\<close>
    by simp
  have pr: "primitive_root (2 ^ l) (2 [^]\<^bsub>Fn\<^esub> s)"
    unfolding assms(2) by (intro two_powers_primitive_root assms \<open>i \<le> k\<close>)

  from fft_ifft_correct'[OF \<open>length a = 2 ^ l\<close> \<open>l \<le> k + 1\<close> \<open>set a \<subseteq> fermat_non_unique_carrier\<close>]
  have "map to_residue_ring (fft_ifft it s a) = FNTT'' ?\<mu> (map to_residue_ring a)"
    by simp
  also have "... = FNTT' ?\<mu> (map to_residue_ring a)"
    apply (intro FNTT''_FNTT')
    using assms(1) by simp
  also have "... = FNTT ?\<mu> (map to_residue_ring a)"
    by (intro FNTT'_FNTT)
  also have "... = NTT ?\<mu> (map to_residue_ring a)"
    apply (intro FNTT_NTT[of _ "2 ^ l" l])
    subgoal by (intro nat_pow_closed two_in_carrier prop_ifI[where P = "\<lambda>x. x \<in> carrier Fn"] Units_inv_closed two_is_unit)
    subgoal by argo
    subgoal
    proof (cases it)
      case True
      then show ?thesis unfolding it_unfold(1)[OF True]
      apply (intro primitive_root_inv)
      subgoal by simp
      subgoal by (rule pr)
      done
    next
      case False
      then show ?thesis unfolding it_unfold(2)[OF False] by (intro pr)
    qed
    subgoal
    proof (cases it)
      case True
      show ?thesis unfolding it_unfold(1)[OF True]
        by (intro inv_halfway_property Units_pow_closed two_is_unit pow_2sl)
    next
      case False
      then show ?thesis
        unfolding it_unfold(2)[OF False] by (intro pow_2sl)
    qed
    subgoal using assms(1) by simp
    subgoal apply (intro set_subseteqI) using to_residue_ring_in_carrier by simp
    done
  finally show ?thesis .
qed

lemma fft_correct:
  assumes "length a = 2 ^ l"
  assumes "s = 2 ^ i"
  assumes "i + l = k + 1"
  assumes "l > 0"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "map to_residue_ring (fft s a) = NTT (2 [^]\<^bsub>Fn\<^esub> s) (map to_residue_ring a)"
  unfolding fft.simps using fft_ifft_correct[OF assms] by simp

lemma ifft_correct:
  assumes "length a = 2 ^ l"
  assumes "s = 2 ^ i"
  assumes "i + l = k + 1"
  assumes "l > 0"
  assumes "set a \<subseteq> fermat_non_unique_carrier"
  shows "map to_residue_ring (ifft s a) = NTT ((inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> s) (map to_residue_ring a)"
  unfolding ifft.simps using fft_ifft_correct[OF assms] by simp

end

end