subsection "Final Preparations"

theory Schoenhage_Strassen
imports
  Main
  "HOL-Algebra.IntRing"
  "HOL-Algebra.QuotRing"
  "HOL-Algebra.Chinese_Remainder"
  "HOL-Algebra.Ring"
  "HOL-Algebra.Polynomials"
  "Word_Lib.Bit_Comprehension"
  Z_mod_power_of_2
  Z_mod_Fermat
  "Karatsuba.Nat_LSBF"
  "Karatsuba.Karatsuba_Sum_Lemmas"
  "Karatsuba.Karatsuba"
  "../Preliminaries/Schoenhage_Strassen_Ring_Lemmas"
begin

lemma aux_ineq_1: "n > 1 \<Longrightarrow> 2 ^ (2 * n - 1) > n + 1 + 2 ^ n"
proof -
  have 1: "\<And>k. 2 ^ (2 * (k + 2) - 1) > (k + 2) + 1 + 2 ^ (k + 2)"
    subgoal for k
      by (induction k) simp_all
    done
  assume \<open>n > 1\<close>
  then obtain k where "n = k + 2"
    by (metis Suc_eq_plus1_left add_2_eq_Suc' less_natE)
  then show ?thesis using 1 by blast
qed
lemma aux_ineq_2: "n > 2 \<Longrightarrow> 2 ^ (2 * n - 2) > n + 2 ^ n"
proof -
  have 1: "\<And>k. 2 ^ (2 * (k + 3) - 2) \<ge> (k + 3) + 2 ^ (k + 3) + 1"
    subgoal for k
    proof (induction k)
      case (Suc k)
      have "2 ^ (Suc k + 3) \<ge> Suc k + 3" by simp
      then have "4 * k + 16 + 2 ^ (Suc k + 3) \<ge> (Suc k + 3) + 1"
        by simp
      then have "(Suc k + 3) + 2 ^ (Suc k + 3) + 1 \<le> 4 * k + 16 + 2 * 2 ^ (Suc k + 3)"
        by simp
      also have "... = 4 * k + 4 * 4 + 2 * 2 ^ (Suc (k + 3))" by simp
      also have "... = 4 * k + 4 * 4 + 2 * 2 * 2 ^ (k + 3)"
        apply (intro arg_cong2[where f = "(+)"] refl)
        using power_Suc mult.assoc by metis
      also have "... = 4 * (k + 3 + 2 ^ (k + 3) + 1)" by simp
      also have "... \<le> 4 * 2 ^ (2 * (k + 3) - 2)" using Suc.IH by simp
      also have "... = 2 ^ ((2 * (k + 3)) - 2 + 2)" by (simp add: power_add) 
      also have "... = 2 ^ (2 * (Suc k + 3) - 2)" by simp
      finally show ?case .
    qed simp
    done
  assume "n > 2"
  then have "n \<ge> 3" by simp
  then obtain k where "n = k + 3"
    by (metis add.commute le_Suc_ex)
  then show ?thesis using 1
    by (metis add_lessD1 le_eq_less_or_eq less_add_one)
qed
lemma aux_ineq_3: "n > 1 \<Longrightarrow> 2 ^ n \<ge> n + 2"
proof -
  have 1: "\<And>k. 2 ^ (k + 2) \<ge> (k + 2) + 2"
    subgoal for k
      by (induction k) simp_all
    done
  assume \<open>n > 1\<close>
  then obtain k where "n = k + 2"
    by (metis Suc_eq_plus1_left add_2_eq_Suc' less_natE)
  then show ?thesis using 1 by blast
qed

lemma (in residues) nat_embedding_eq: "ring.nat_embedding R x = int x mod m"
  apply (induction x)
  subgoal by (simp add: zero_cong)
  subgoal for x by (simp add: res_add_eq one_cong mod_add_eq add.commute)
  done

lemma (in residues) carrier_mod_eq: "x \<in> carrier R \<Longrightarrow> x mod m = x"
  unfolding res_carrier_eq by simp

text "The Schoenhage-Strassen Multiplication in $\\mathbb{Z}_{F_m}$ works recursively.
In the following, we will state some lemmas that will be useful in the recursion case
($m \\geq 3$)."

locale m_lemmas =
  fixes m :: nat
  assumes m_ge_3: "\<not> m < 3"
begin

text "Lemmas in @{type nat} resp. @{type int}."

lemma m_gt_0: "m > 0" using m_ge_3 by simp

definition n :: nat where
"n \<equiv> (if odd m then (m + 1) div 2 else (m + 2) div 2)"

definition oe_n :: nat where
"oe_n \<equiv> (if odd m then n + 1 else n)"

lemma n_gt_1: "n > 1" unfolding n_def using m_ge_3 by simp
lemma n_ge_2: "n \<ge> 2" using n_gt_1 by simp
lemma n_gt_0: "n > 0" using n_gt_1 by simp
lemma even_m_imp_n_ge_3: "even m \<Longrightarrow> n \<ge> 3" unfolding n_def using m_ge_3 by auto

lemma n_lt_m: "n < m" unfolding n_def using m_ge_3 by auto

lemma oe_n_gt_1: "oe_n > 1" unfolding oe_n_def using n_gt_1 by simp
lemma oe_n_gt_0: "oe_n > 0" using oe_n_gt_1 by simp

lemma oe_n_le_n: "oe_n \<le> n + 1" unfolding oe_n_def by simp
lemma oe_n_minus_1_le_n: "oe_n - 1 \<le> n" unfolding oe_n_def by simp

lemma two_pow_oe_n_div_2: "(2::nat) ^ oe_n div 2 = 2 ^ (oe_n - 1)"
  by (simp add: Suc_leI power_diff oe_n_gt_0)
lemma two_pow_oe_n_as_halves: "(2::nat) ^ oe_n = 2 ^ (oe_n - 1) + 2 ^ (oe_n - 1)"
  using two_pow_oe_n_div_2 oe_n_gt_0
  by (metis add_self_div_2 div_add dvd_power)
lemma two_pow_Suc_oe_n_as_prod: "(2::nat) ^ (oe_n + 1) = 4 * 2 ^ (oe_n - 1)"
  using oe_n_gt_0 by (simp add: power_eq_if)

lemma index_intros:
  fixes i :: nat
  assumes "i < 2 ^ (oe_n - 1)"
  shows "i < 2 ^ oe_n" "2 ^ (oe_n - 1) + i < 2 ^ oe_n"
  using assms two_pow_oe_n_as_halves by simp_all

lemma index_decomp:
  assumes "j < (2::nat) ^ (oe_n + 1)"
  shows
    "j div 2 ^ (oe_n - 1) < 4"
    "j mod 2 ^ (oe_n - 1) < 2 ^ (oe_n - 1)"
    "j = (j div 2 ^ (oe_n - 1)) * 2 ^ (oe_n - 1) + (j mod 2 ^ (oe_n - 1))"
  using assms two_pow_Suc_oe_n_as_prod
  by (simp_all add: less_mult_imp_div_less div_mod_decomp)
lemma index_comp:
  fixes i j :: nat
  assumes "i < 4" "j < 2 ^ (oe_n - 1)"
  shows
    "i * 2 ^ (oe_n - 1) + j < 2 ^ (oe_n + 1)"
    "(i * 2 ^ (oe_n - 1) + j) div 2 ^ (oe_n - 1) = i"
    "(i * 2 ^ (oe_n - 1) + j) mod 2 ^ (oe_n - 1) = j"
proof -
  from assms have "i \<le> 3" by simp
  then have "i * 2 ^ (oe_n - 1) + j < 3 * 2 ^ (oe_n - 1) + 2 ^ (oe_n - 1)"
    using \<open>j < 2 ^ (oe_n - 1)\<close>
    using nat_less_add_iff2 trans_less_add2 by blast
  then show "i * 2 ^ (oe_n - 1) + j < 2 ^ (oe_n + 1)"
    unfolding two_pow_Suc_oe_n_as_prod by simp
  show "(i * 2 ^ (oe_n - 1) + j) div 2 ^ (oe_n - 1) = i"
    using assms by simp
  show "(i * 2 ^ (oe_n - 1) + j) mod 2 ^ (oe_n - 1) = j"
    using assms by simp
qed

lemma mn:
  "odd m \<Longrightarrow> m = 2 * n - 1"
  "even m \<Longrightarrow> m = 2 * n - 2"
  using n_def by simp_all

lemma m0: "m = (n - 1) + (oe_n - 1)"
  unfolding oe_n_def using n_gt_0 mn
  by auto
lemma m1: "m + 1 = (n - 1) + oe_n"
  using m0 oe_n_gt_0 by linarith

lemma two_pow_m1_as_prod: "(2::nat) ^ (m + 1) = 2 ^ (n - 1) * 2 ^ oe_n"
  by (simp only: power_add[symmetric] m1)
lemma two_pow_m0_as_prod: "(2::nat) ^ m = 2 ^ (n - 1) * 2 ^ (oe_n - 1)"
  using m0 by (simp only: power_add[symmetric])

lemma two_pow_two_n_le: "(2::nat) ^ (2 * n) \<le> 2 * 2 ^ (m + 1)"
proof -
  have "(2::nat) ^ (2 * n) = 2 ^ (2 * n - 2 + 2)"
    apply (intro arg_cong2[where f = power] refl)
    using n_gt_1 by linarith
  also have "... = 2 ^ 2 * 2 ^ (2 * n - 2)" by simp
  also have "... \<le> 2 ^ 2 * 2 ^ m" using mn by (cases "odd m"; simp)
  finally show ?thesis by simp
qed

lemma oe_n_m_bound_0: "oe_n + 2 ^ n < 2 ^ m"
proof (cases "odd m")
  case True
  then have "m = 2 * n - 1" "oe_n = n + 1" using mn oe_n_def by simp_all
  then show ?thesis using aux_ineq_1[OF n_gt_1] by argo
next
  case False
  then have "m = 2 * n - 2" "oe_n = n" "n > 2" using mn oe_n_def even_m_imp_n_ge_3
    by simp_all
  then show ?thesis using aux_ineq_2[OF \<open>n > 2\<close>] by argo
qed
lemma oe_n_m_bound_1: "oe_n + 1 + 2 ^ n \<le> 2 ^ m"
  using oe_n_m_bound_0 by simp
lemma two_pow_oe_n_m_bound_1: "(2::'a::linordered_semidom) ^ (oe_n + 1 + 2 ^ n) \<le> 2 ^ 2 ^ m"
  by (intro power_increasing oe_n_m_bound_1) simp
lemma two_pow_oe_n_m_bound_0_int: "2 ^ (oe_n + 2 ^ n) < int_lsbf_fermat.n m"
  by (metis oe_n_m_bound_0 one_less_numeral_iff power_strict_increasing_iff semiring_norm(76) trans_less_add1)
lemma two_pow_oe_n_m_bound_1_int: "2 ^ (oe_n + 1 + 2 ^ n) < int_lsbf_fermat.n m"
  using two_pow_oe_n_m_bound_1
  by (metis le_eq_less_or_eq less_add_one trans_less_add1)

lemma oe_n_n_bound_1: "oe_n + 1 + 2 ^ n \<le> 2 ^ (n + 1)"
proof -
  have "oe_n + 1 + 2 ^ n \<le> n + 2 + 2 ^ n" unfolding oe_n_def by simp
  also have "... \<le> 2 ^ n + 2 ^ n"
    by (intro add_mono order.refl aux_ineq_3 n_gt_1)
  also have "... = 2 ^ (n + 1)" by simp
  finally show ?thesis .
qed

definition pad_length where "pad_length = 3 * n + 5"

text "Lemmas using residue rings."

definition Zn where "Zn = residue_ring (int_lsbf_mod.n (n + 2))"
definition Fn where "Fn = residue_ring (int_lsbf_fermat.n n)"
definition Fm where "Fm = residue_ring (int_lsbf_fermat.n m)"

text "Lemmas in $\\mathbb{Z}_{2 ^ {n + 2}}$"

sublocale Znr : int_lsbf_mod "n + 2"
  rewrites "Znr.Zn \<equiv> Zn"
proof -
  show "int_lsbf_mod (n + 2)" by unfold_locales simp
  then interpret A : int_lsbf_mod "n + 2" .
  show "A.Zn \<equiv> Zn" unfolding Zn_def A.Zn_def .
qed

text "Lemmas in $\\mathbb{Z}_{F_m}$ resp. $\\mathbb{Z}_{F_n}$."

sublocale Fnr : int_lsbf_fermat n
  rewrites "Fnr.Fn \<equiv> Fn"
  subgoal unfolding int_lsbf_fermat.Fn_def Fn_def .
  done

sublocale Fnr_M : multiplicative_subgroup Fn "Units Fn" "units_of Fn"
  by (rule Fnr.units_subgroup)

sublocale Fmr : int_lsbf_fermat m
  rewrites "Fmr.Fn \<equiv> Fm"
  subgoal unfolding int_lsbf_fermat.Fn_def Fm_def .
  done

sublocale Fmr_M : multiplicative_subgroup Fm "Units Fm" "units_of Fm"
  by (rule Fmr.units_subgroup)

lemma two_pow_oe_n_primitive_root_Fm:
  "Fmr.primitive_root (2 ^ oe_n) (2 [^]\<^bsub>Fm\<^esub> (2::nat) ^ (n - 1))"
  apply (intro Fmr.two_powers_primitive_root)
  subgoal using m1 by argo
  subgoal using n_lt_m by simp
  done
lemma two_pow_oe_n_root_of_unity_Fm:
  "Fmr.root_of_unity (2 ^ oe_n) (2 [^]\<^bsub>Fm\<^esub> (2::nat) ^ (n - 1))"
  using two_pow_oe_n_primitive_root_Fm by simp

lemma four_prim_root_Fn: "Fnr.primitive_root (2 ^ n) (2 [^]\<^bsub>Fn\<^esub> (2::nat))"
  using Fnr.primitive_root_recursion[OF _ Fnr.two_is_primitive_root] by simp

lemma two_oe_n: "2 [^]\<^bsub>Fn\<^esub> oe_n = 2 ^ oe_n"
proof -
  have "2 ^ n \<ge> n + 1" using aux_ineq_3[OF n_gt_1] by simp
  then have "2 ^ n \<ge> oe_n" unfolding oe_n_def by simp
  then have "(2::int) ^ oe_n \<le> 2 ^ 2 ^ n" by simp
  then have two_oe_n_mod_Fn: "2 ^ oe_n mod int Fnr.n = 2 ^ oe_n"
    using zle_iff_zadd by auto
  then show ?thesis unfolding Fnr.pow_nat_eq .
qed
lemma two_oe_n_Units_Fn: "2 ^ oe_n \<in> Units Fn"
  apply (intro Fnr.two_powers_Units)
  unfolding oe_n_def using aux_ineq_3[OF n_gt_1] by simp
lemma two_oe_n_carrier_Fn: "2 ^ oe_n \<in> carrier Fn"
  by (intro Fnr.Units_closed two_oe_n_Units_Fn)

definition prim_root_exponent :: nat where "prim_root_exponent = (if odd m then 1 else 2)"
definition \<mu> where "\<mu> = 2 [^]\<^bsub>Fn\<^esub> prim_root_exponent"

lemma \<mu>_Units_Fn: "\<mu> \<in> Units Fn"
  unfolding \<mu>_def by (intro Fnr.Units_pow_closed Fnr.two_is_unit)
lemma \<mu>_carrier_Fn: "\<mu> \<in> carrier Fn"
  by (intro Fnr.Units_closed \<mu>_Units_Fn)

lemma \<mu>_prim_root: "Fnr.primitive_root (2 ^ oe_n) \<mu>"
proof (cases "odd m")
  case True
  then show ?thesis unfolding oe_n_def \<mu>_def prim_root_exponent_def
    using Fnr.two_in_carrier Fnr.two_is_primitive_root by simp
next
  case False
  then show ?thesis unfolding oe_n_def \<mu>_def prim_root_exponent_def
    using four_prim_root_Fn by simp
qed
lemma \<mu>_root_of_unity: "Fnr.root_of_unity (2 ^ oe_n) \<mu>"
  using \<mu>_prim_root by simp
lemma \<mu>_halfway_property: "\<mu> [^]\<^bsub>Fn\<^esub> ((2::nat) ^ oe_n div 2) = \<ominus>\<^bsub>Fn\<^esub> \<one>\<^bsub>Fn\<^esub>"
proof -
  have "prim_root_exponent * (2 ^ oe_n div 2) = 2 ^ n"
    unfolding prim_root_exponent_def oe_n_def
    using n_gt_1 by simp
  then have "\<mu> [^]\<^bsub>Fn\<^esub> ((2::nat) ^ oe_n div 2) = 2 [^]\<^bsub>Fn\<^esub> ((2::nat) ^ n)"
    unfolding \<mu>_def by (simp add: Fnr.nat_pow_pow[OF Fnr.two_in_carrier])
  then show ?thesis
    using Fnr.two_pow_half_carrier_length_residue_ring
    unfolding Fn_def[symmetric] by argo
qed

end

text "Lemmas only depending on one of the input arguments (and $m$)."

locale carrier_input = m_lemmas + 
  fixes num :: nat_lsbf
  assumes num_carrier: "num \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
begin

definition num_blocks where "num_blocks = subdivide (2 ^ (n - 1)) num"
definition num_blocks_carrier where "num_blocks_carrier = map (fill (2 ^ (n + 1))) num_blocks"
definition num_Zn where "num_Zn = map Znr.reduce num_blocks"
definition num_Zn_pad where "num_Zn_pad = concat (map (fill pad_length) num_Zn)"
definition num_dft where "num_dft = Fnr.fft prim_root_exponent num_blocks_carrier"
definition num_dft_odds where "num_dft_odds = evens_odds False num_dft"

lemmas defs = num_blocks_def num_blocks_carrier_def num_Zn_def num_Zn_pad_def num_dft_def num_dft_odds_def

lemma length_num[simp]: "length num = 2 ^ (m + 1)"
  using num_carrier by (elim Fmr.fermat_non_unique_carrierE)

lemma length_num_blocks[simp]: "length num_blocks = 2 ^ oe_n"
  apply (unfold num_blocks_def)
  apply (intro conjunct1[OF subdivide_correct])
  using two_pow_m1_as_prod by simp_all
lemma length_nth_num_blocks[simp]:
  fixes i :: nat
  assumes "i < 2 ^ oe_n"
  shows "length (num_blocks ! i) = 2 ^ (n - 1)"
  apply (intro mp[OF conjunct2[OF subdivide_correct[of "2 ^ (n - 1)" num "2 ^ oe_n"]]])
  subgoal by simp
  subgoal using length_num two_pow_m1_as_prod by argo
  subgoal using assms length_num_blocks unfolding num_blocks_def[symmetric] by simp
  done
lemma num_blocks_bound[simp]:
  fixes i :: nat
  assumes "i < 2 ^ oe_n"
  shows "Nat_LSBF.to_nat (num_blocks ! i) < 2 ^ 2 ^ (n - 1)"
  using length_nth_num_blocks[OF assms] to_nat_length_bound by metis
lemma num_blocks_carrier_Fm[simp]:
  fixes i :: nat
  assumes "i < 2 ^ oe_n"
  shows "int (Nat_LSBF.to_nat (num_blocks ! i)) \<in> carrier Fm"
  unfolding Fmr.res_carrier_eq atLeastAtMost_iff
proof (intro conjI)
  show "0 \<le> int (Nat_LSBF.to_nat (num_blocks ! i))" by simp
  have "int (Nat_LSBF.to_nat (num_blocks ! i)) < 2 ^ 2 ^ (n - 1)"
    using num_blocks_bound[OF assms] by simp
  also have "... < 2 ^ 2 ^ m" using n_lt_m by simp
  finally show "int (Nat_LSBF.to_nat (num_blocks ! i)) \<le> int (2 ^ 2 ^ m + 1) - 1" by simp
qed

lemma length_num_blocks_carrier[simp]: "length num_blocks_carrier = 2 ^ oe_n"
  unfolding num_blocks_carrier_def by simp

lemma to_res_num: "Fmr.to_residue_ring num = (\<Oplus>\<^bsub>Fm\<^esub>j \<leftarrow> [0..<2 ^ oe_n].
      map (int \<circ> Nat_LSBF.to_nat) num_blocks ! j \<otimes>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ (n - 1))) [^]\<^bsub>Fm\<^esub> j))"
proof -
  let ?m = "int Fmr.n"
  have "(\<Oplus>\<^bsub>Fm\<^esub>j \<leftarrow> [0..<2 ^ oe_n].
      map (int \<circ> Nat_LSBF.to_nat) num_blocks ! j \<otimes>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ (n - 1))) [^]\<^bsub>Fm\<^esub> j)) =
    (\<Oplus>\<^bsub>Fm\<^esub>j \<leftarrow> [0..<2 ^ oe_n].
      map (int \<circ> Nat_LSBF.to_nat) num_blocks ! j \<otimes>\<^bsub>Fm\<^esub> (2 [^]\<^bsub>Fm\<^esub> (j * (2::nat) ^ (n - 1))))"
    apply (intro_cong "[cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>)]" more: refl Fmr.monoid_sum_list_cong)
    unfolding Fmr.nat_pow_pow[OF Fmr.two_in_carrier]
    by (intro arg_cong2[where f = "([^]\<^bsub>Fm\<^esub>)"] refl mult.commute)
  also have "... = (\<Sum>j\<leftarrow>[0..<2 ^ oe_n].
      map (int \<circ> Nat_LSBF.to_nat) num_blocks ! j * (2 ^ (j * 2 ^ (n - 1)) mod ?m) mod ?m) mod ?m"
    unfolding Fmr.monoid_sum_list_eq_sum_list Fmr.res_mult_eq Fmr.pow_nat_eq by (rule refl)

  also have "... = (\<Sum>j \<leftarrow> [0..<2 ^ oe_n].
      (map (int \<circ> Nat_LSBF.to_nat) num_blocks ! j * 2 ^ (j * 2 ^ (n - 1)))) mod ?m"
    by (simp only: mod_mult_right_eq sum_list_mod)
  also have "... = (\<Sum>j \<leftarrow> [0..<2 ^ oe_n].
      (int (Nat_LSBF.to_nat (num_blocks ! j)) * (2 ^ (j * 2 ^ (n - 1))))) mod ?m"
    by (intro_cong "[cong_tag_2 (mod), cong_tag_2 (*)]" more: refl semiring_1_sum_list_eq)
        simp_all
  also have "... = int (\<Sum>j \<leftarrow> [0..<2 ^ oe_n].
      (Nat_LSBF.to_nat (num_blocks ! j) * (2 ^ (j * 2 ^ (n - 1))))) mod ?m"
    by (simp add: sum_list_int)
  also have "... = int (Nat_LSBF.to_nat num) mod ?m"
    unfolding num_blocks_def
    apply (intro arg_cong[where f = "\<lambda>i. i mod ?m"] arg_cong[where f = int])
    apply (intro to_nat_subdivide[symmetric])
    subgoal by simp
    subgoal by (simp only: length_num two_pow_m1_as_prod)
    done
  finally show ?thesis unfolding Fmr.to_residue_ring.simps by argo
qed

lemma length_num_Zn[simp]: "length num_Zn = 2 ^ oe_n"
  unfolding num_Zn_def using length_num_blocks by simp
lemma length_nth_num_Zn[simp]:
  fixes i :: nat
  assumes "i < 2 ^ oe_n"
  shows "length (num_Zn ! i) = n + 2"
  unfolding num_Zn_def using length_num_blocks Znr.length_reduce assms by simp

lemma length_num_Zn_pad[simp]: "length num_Zn_pad = pad_length * 2 ^ oe_n"
  unfolding num_Zn_pad_def length_concat
proof -
  have "sum_list (map length (map (fill pad_length) num_Zn)) =
    sum_list (map (length \<circ> (fill pad_length)) num_Zn)"
    by simp
  also have "... = sum_list (map (\<lambda>j. pad_length) num_Zn)"
  proof (intro arg_cong[where f = sum_list] map_cong refl)
    fix x
    assume "x \<in> set num_Zn"
    then obtain i where "i < 2 ^ oe_n" "x = num_Zn ! i" using length_num_Zn
      by (metis in_set_conv_nth)
    then have "length x = n + 2" using length_nth_num_Zn by simp
    then show "(length \<circ> fill pad_length) x = pad_length" using length_fill pad_length_def by simp
  qed
  also have "... = pad_length * 2 ^ oe_n"
    using length_num_Zn sum_list_triv[of pad_length num_Zn] by simp
  finally show "sum_list (map length (map (fill pad_length) num_Zn)) = ..." .
qed

lemma to_nat_num_Zn_pad:
  "Nat_LSBF.to_nat num_Zn_pad = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. Nat_LSBF.to_nat (num_Zn ! i) * 2 ^ (i * pad_length))"
proof -
  have "Nat_LSBF.to_nat num_Zn_pad = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. Nat_LSBF.to_nat (subdivide pad_length num_Zn_pad ! i) * 2 ^ (i * pad_length))"
    using length_num_Zn_pad by (intro to_nat_subdivide length_num_Zn_pad) (simp add: pad_length_def)
  also have "subdivide pad_length num_Zn_pad = map (fill pad_length) num_Zn"
    unfolding num_Zn_pad_def
    apply (intro subdivide_concat)
    by (simp_all add: Znr.length_reduce length_fill pad_length_def)
  also have "(\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. Nat_LSBF.to_nat (map (fill pad_length) num_Zn ! i) * 2 ^ (i * pad_length))
    = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. Nat_LSBF.to_nat (num_Zn ! i) * 2 ^ (i * pad_length))"
    apply (intro semiring_1_sum_list_eq arg_cong2[where f = "(*)"] refl)
    using length_num_Zn by simp
  finally show ?thesis .
qed

lemma length_num_dft[simp]: "length num_dft = 2 ^ oe_n"
  unfolding num_dft_def
  by (intro Fnr.length_fft) simp

lemma fill_num_blocks_carrier[simp]: "set num_blocks_carrier \<subseteq> Fnr.fermat_non_unique_carrier"
  apply (intro set_subseteqI Fnr.fermat_non_unique_carrierI)
  by (simp only: num_blocks_carrier_def length_num_blocks length_map nth_map length_fill length_nth_num_blocks power_increasing[of "n - 1" "n + 1" "2::nat"])

lemma num_dft_carrier[simp]: "set num_dft \<subseteq> Fnr.fermat_non_unique_carrier"
  unfolding num_dft_def
  apply (intro Fnr.fft_carrier[of _ oe_n])
  subgoal by simp
  subgoal by (rule fill_num_blocks_carrier)
  done

lemma to_res_num_dft:
  "map Fnr.to_residue_ring num_dft = Fnr.NTT \<mu> (map Fnr.to_residue_ring num_blocks_carrier)"
  unfolding num_dft_def \<mu>_def prim_root_exponent_def
  apply (intro Fnr.fft_correct[of _ oe_n _ "if odd m then 0 else 1"])
  subgoal by simp
  subgoal unfolding prim_root_exponent_def by simp
  subgoal unfolding oe_n_def by simp
  subgoal by (rule oe_n_gt_0)
  subgoal by (rule fill_num_blocks_carrier)
  done

lemma length_num_dft_odds[simp]: "length num_dft_odds = 2 ^ (oe_n - 1)"
  unfolding num_dft_odds_def
  by (simp add: length_evens_odds two_pow_oe_n_as_halves)
lemma num_dft_odds_carrier[simp]: "set num_dft_odds \<subseteq> Fnr.fermat_non_unique_carrier"
  unfolding num_dft_odds_def using set_evens_odds num_dft_carrier by fastforce

end

subsubsection "A special residue problem"

definition solve_special_residue_problem where
"solve_special_residue_problem n \<xi> \<eta> =
    (let \<delta> = int_lsbf_mod.subtract_mod (n + 2) \<eta> (take (n + 2) \<xi>) in
    add_nat \<xi> (add_nat (\<delta> >>\<^sub>n (2 ^ n)) \<delta>))"

lemma two_pow_n_geq_n_plus_2: "n \<ge> 2 \<Longrightarrow> 2 ^ n \<ge> n + 2"
proof -
  have aux: "\<And>k. 2 ^ (k + 2) \<ge> k + 4"
    subgoal for k
      by (induction k) simp_all
    done
  assume "n \<ge> 2"
  then obtain k where "n = k + 2" by (metis le_add_diff_inverse2)
  then show ?thesis using aux[of k] by presburger
qed

lemma fermat_mod_pow_2_aux: "n \<ge> 2 \<Longrightarrow> (2::nat) ^ (2 ^ n) mod 2 ^ (n + 2) = 0"
proof -
  assume "n \<ge> 2"
  then show ?thesis using two_pow_n_geq_n_plus_2[of n]
    by (meson dvd_imp_mod_0 le_imp_power_dvd)
qed

definition solves_special_residue_problem where
"solves_special_residue_problem z n \<xi> \<eta> \<equiv>
    z < 2 ^ (n + 2) * int_lsbf_fermat.n n
    \<and> z mod int_lsbf_fermat.n n = \<xi>
    \<and> z mod (2 ^ (n + 2)) = \<eta>"

lemma solve_special_residue_problem_correct:
  fixes n :: nat
  fixes \<xi> \<eta> :: nat_lsbf
  assumes "n \<ge> 2"
  assumes "length \<eta> \<le> n + 2"
  assumes "Nat_LSBF.to_nat \<xi> < int_lsbf_fermat.n n"
  assumes "z = solve_special_residue_problem n \<xi> \<eta>"
  shows "solves_special_residue_problem (Nat_LSBF.to_nat z) n (Nat_LSBF.to_nat \<xi>) (Nat_LSBF.to_nat \<eta>)"
  unfolding solves_special_residue_problem_def
proof (intro conjI)
  define \<delta> where "\<delta> = int_lsbf_mod.subtract_mod (n + 2) \<eta> (take (n + 2) \<xi>)"
  then have "z = \<xi> +\<^sub>n ((\<delta> >>\<^sub>n (2 ^ n)) +\<^sub>n \<delta>)"
    using assms(4) by (simp add: Let_def solve_special_residue_problem_def)
  then have "Nat_LSBF.to_nat z = Nat_LSBF.to_nat \<xi> + (2 ^ (2 ^ n) * Nat_LSBF.to_nat \<delta> + Nat_LSBF.to_nat \<delta>)"
    by (simp add: add_nat_correct to_nat_app)
  then have 0: "Nat_LSBF.to_nat z = Nat_LSBF.to_nat \<xi> + int_lsbf_fermat.n n * Nat_LSBF.to_nat \<delta>"
    by simp

  then have "Nat_LSBF.to_nat z mod int_lsbf_fermat.n n = Nat_LSBF.to_nat \<xi> mod int_lsbf_fermat.n n"
    by presburger
  also have "... = Nat_LSBF.to_nat \<xi>"
    using assms(3) by simp
  finally show "Nat_LSBF.to_nat z mod int_lsbf_fermat.n n = Nat_LSBF.to_nat \<xi>" .

  have "int_lsbf_fermat.n n mod 2 ^ (n + 2) = 1"
    using assms(1) fermat_mod_pow_2_aux[of n]
    by (metis Nat.add_0_right add.left_commute add_lessD1 less_exp mod_add_right_eq mod_less nat_1_add_1)
  then have 1: "int (int_lsbf_fermat.n n) mod 2 ^ (n + 2) = 1"
    by (metis int_ops(2) of_nat_numeral of_nat_power zmod_int)

  interpret Znr: int_lsbf_mod "n + 2"
    apply unfold_locales by simp

  have "int (Nat_LSBF.to_nat \<delta>) mod int Znr.n = Znr.to_residue_ring \<delta>"
    by (rule Znr.to_residue_ring_def[symmetric])
  also have "... = Znr.to_residue_ring \<eta> \<ominus>\<^bsub>Znr.Zn\<^esub> Znr.to_residue_ring (take (n + 2) \<xi>)"
    unfolding \<delta>_def
    apply (intro Znr.subtract_mod_correct)
    subgoal using assms by argo
    subgoal by simp
    subgoal using Znr.m_gt_one by linarith
    done
  also have "... = (int (Nat_LSBF.to_nat \<eta>) - int (Nat_LSBF.to_nat \<xi>)) mod int Znr.n"
    unfolding Znr.residues_minus_eq Znr.to_residue_ring_def to_nat_take
    by (simp add: mod_diff_eq zmod_int)
  finally have 2: "int (Nat_LSBF.to_nat \<delta>) mod int Znr.n = ..." .

  have "Nat_LSBF.to_nat \<eta> < 2 ^ (n + 2)" using \<open>length \<eta> \<le> n + 2\<close> to_nat_length_bound[of \<eta>] power_increasing[of "length \<eta>" "n + 2" "2::nat"]
    by linarith
  from 0 have "int (Nat_LSBF.to_nat z) mod Znr.n = (int (Nat_LSBF.to_nat \<xi>) + int_lsbf_fermat.n n * int (Nat_LSBF.to_nat \<delta>)) mod Znr.n"
    using int_ops(7) int_plus by presburger
  also have "... = (int (Nat_LSBF.to_nat \<xi>) mod Znr.n + (int (int_lsbf_fermat.n n) mod Znr.n) * (int (Nat_LSBF.to_nat \<delta>) mod Znr.n)) mod Znr.n"
    by (simp only: mod_add_eq[of "int (Nat_LSBF.to_nat \<xi>)" Znr.n, symmetric]
        mod_mult_eq[of "int (int_lsbf_fermat.n n)" Znr.n, symmetric]
        mod_add_right_eq)
  also have "... = (int (Nat_LSBF.to_nat \<xi>) mod Znr.n + (int (Nat_LSBF.to_nat \<delta>) mod Znr.n)) mod Znr.n"
    apply (intro_cong "[cong_tag_2 (mod), cong_tag_2 (+)]" more: refl)
    using 1 by simp
  also have "... = (int (Nat_LSBF.to_nat \<xi>) mod Znr.n + (int (Nat_LSBF.to_nat \<eta>) mod Znr.n - int (Nat_LSBF.to_nat \<xi>) mod Znr.n)) mod Znr.n"
    using 2 by (simp add: mod_simps)
  also have "... = int (Nat_LSBF.to_nat \<eta>) mod 2 ^ (n + 2)"
    by simp
  also have "... = int (Nat_LSBF.to_nat \<eta>)" using \<open>Nat_LSBF.to_nat \<eta> < 2 ^ (n + 2)\<close>
    by (metis mod_less of_nat_mod real_of_nat_eq_numeral_power_cancel_iff)
  finally have "int (Nat_LSBF.to_nat z) mod Znr.n = int (Nat_LSBF.to_nat \<eta>)" .
  then show "Nat_LSBF.to_nat z mod 2 ^ (n + 2) = Nat_LSBF.to_nat \<eta>"
    by (metis nat_int_comparison(1) zmod_int)

  show "Nat_LSBF.to_nat z < 2 ^ (n + 2) * int_lsbf_fermat.n n"
  proof -
    have "int (Nat_LSBF.to_nat z) = int (Nat_LSBF.to_nat \<xi>) + int (int_lsbf_fermat.n n) * int (Nat_LSBF.to_nat \<delta>)"
      using 0 
      using int_ops(7) int_plus by presburger
    also have "... \<le> (2::int) ^ (2 ^ n) + int (int_lsbf_fermat.n n) * int (Nat_LSBF.to_nat \<delta>)"
      using assms(3) by simp
    also have "int (int_lsbf_fermat.n n) * int (Nat_LSBF.to_nat \<delta>) \<le> int (int_lsbf_fermat.n n) * ((2::int) ^ (n + 2) - 1)"
    proof -
      have "length \<delta> \<le> n + 2"
        unfolding \<delta>_def
        apply (intro Znr.length_subtract_mod \<open>length \<eta> \<le> n + 2\<close>)
        using Znr.length_reduce by simp
      have "Nat_LSBF.to_nat \<delta> \<le> 2 ^ (n + 2) - 1"
        using to_nat_length_upper_bound[of \<delta>] power_increasing[OF \<open>length \<delta> \<le> n + 2\<close>, of 2]
        using diff_le_mono by fastforce
      then have "int (Nat_LSBF.to_nat \<delta>) \<le> (2::int) ^ (n + 2) - 1"
        using nat_int_comparison(3)[of "Nat_LSBF.to_nat \<delta>" "2 ^ (n + 2) - 1"]
        by (simp add: of_nat_diff)
      then show ?thesis
        using int_lsbf_fermat.n_positive[of n]
        by (meson mult_left_mono of_nat_0_le_iff)
    qed
    finally have "int (Nat_LSBF.to_nat z) \<le> (2::int) ^ (2 ^ n) + (2 ^ (2 ^ n) + 1) * ((2::int) ^ (n + 2) - 1)"
      by force
    also have "... = ((2::int) ^ (2 ^ n) + 1) * 2 ^ (n + 2) - 1"
      apply (simp add: distrib_right)
      apply (simp only: diff_conv_add_uminus[of "(4::int) * 2 ^ n" 1])
      apply (simp only: distrib_left)
      done
    finally have "int (Nat_LSBF.to_nat z) < 2 ^ (n + 2) * (int (int_lsbf_fermat.n n))"
      by (simp add: add.commute mult.commute)
    thus "Nat_LSBF.to_nat z < 2 ^ (n + 2) * int_lsbf_fermat.n n"
      by (metis (mono_tags, lifting) of_nat_less_imp_less of_nat_mult of_nat_numeral of_nat_power)
  qed
qed

lemma fn_zn_coprime: "coprime (int_lsbf_fermat.n n) (2 ^ (n + 2))"
proof -
  consider "n = 0" | "n = 1 " | "n \<ge> 2" by linarith
  then show ?thesis
  proof cases
    case 1
    have "gcd (3::nat) 4 = nat (gcd (3::int) 4)" using gcd_int_int_eq[of 3 4] by simp
    also have "... = gcd 1 3" using gcd_diff1[of "4::int" 3, symmetric] gcd.commute[of "4::int" 3]
      by simp
    also have "... = 1" by simp
    finally show ?thesis unfolding coprime_iff_gcd_eq_1 by (simp add: 1)
  next
    case 2
    have "gcd (5::nat) 8 = nat (gcd (5::int) 8)" using gcd_int_int_eq[of 5 8] by simp
    also have "... = nat (gcd 3 5)" using gcd_diff1[of "8::int" 5] by (simp add: gcd.commute)
    also have "... = nat (gcd 2 3)" using gcd_diff1[of "5::int" 3] by (simp add: gcd.commute)
    also have "... = nat (gcd 1 2)" using gcd_diff1[of "3::int" 2] by (simp add: gcd.commute)
    also have "... = 1" by simp
    finally show ?thesis unfolding coprime_iff_gcd_eq_1 by (simp add: 2)
  next
    case 3
    then have "2 ^ n \<ge> n + 2" by (rule two_pow_n_geq_n_plus_2)
    then obtain k where "2 ^ n = (n + 2) + k" by (meson le_iff_add)
    then have 0: "(2::nat) ^ 2 ^ n = 2 ^ (n + 2) * 2 ^ k" by (simp add: power_add)
    show ?thesis
      unfolding coprime_iff_gcd_eq_1 gcd_red_nat[of "2 ^ 2 ^ n + 1" "2 ^ (n + 2)"]
      unfolding 0 mod_mult_self4
      by simp
  qed
qed

lemma int_ideal_add: "Idl\<^bsub>\<Z>\<^esub> {m} <+>\<^bsub>\<Z>\<^esub> Idl\<^bsub>\<Z>\<^esub> {n} = Idl\<^bsub>\<Z>\<^esub> {gcd m n}"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> Idl\<^bsub>\<Z>\<^esub> {m} <+>\<^bsub>\<Z>\<^esub> Idl\<^bsub>\<Z>\<^esub> {n}"
  then obtain y z where "y \<in> Idl\<^bsub>\<Z>\<^esub> {m}" "z \<in> Idl\<^bsub>\<Z>\<^esub> {n}" "x = y \<oplus>\<^bsub>\<Z>\<^esub> z"
    unfolding AbelCoset.set_add_def Coset.set_mult_def by auto
  then obtain y' z' where "y = y' * m" "z = z' * n"
    using int_Idl by fastforce
  then have 1: "x = y' * m + z' * n" using \<open>x = y \<oplus>\<^bsub>\<Z>\<^esub> z\<close> by simp
  obtain m' where 2: "m = m' * gcd m n"
    by (metis dvdE gcd_dvd1 mult.commute)
  obtain n' where 3: "n = n' * gcd m n"
    by (metis dvdE gcd_dvd2 mult.commute)
  from 1 2 3 have "x = (y' * m' + z' * n') * gcd m n"
    by (simp add: int_distrib(1) mult.assoc)
  then show "x \<in> Idl\<^bsub>\<Z>\<^esub> {gcd m n}" using int_Idl by blast
next
  fix x
  assume "x \<in> Idl\<^bsub>\<Z>\<^esub> {gcd m n}"
  then obtain x' where 1: "x = x' * gcd m n" using int_Idl by fastforce
  obtain s t where "gcd m n = s * m + t * n" using bezout_int by metis
  with 1 have "x = (x' * s) * m \<oplus>\<^bsub>\<Z>\<^esub>  (x' * t) * n"
    by (simp add: int_distrib)
  moreover have "(x' * s) * m \<in> Idl\<^bsub>\<Z>\<^esub> {m}" "(x' * t) * n \<in> Idl\<^bsub>\<Z>\<^esub> {n}"
    using int_Idl by simp_all
  ultimately show "x \<in> Idl\<^bsub>\<Z>\<^esub> {m} <+>\<^bsub>\<Z>\<^esub> Idl\<^bsub>\<Z>\<^esub> {n}"
    unfolding AbelCoset.set_add_def Coset.set_mult_def by auto
qed

lemma int_ideal_inter: "Idl\<^bsub>\<Z>\<^esub> {m} \<inter> Idl\<^bsub>\<Z>\<^esub> {n} = Idl\<^bsub>\<Z>\<^esub> {lcm m n}"
proof -
  have "Idl\<^bsub>\<Z>\<^esub> {m} \<inter> Idl\<^bsub>\<Z>\<^esub> {n} = {u. \<exists>x. u = x * m} \<inter> {u. \<exists>x. u = x * n}"
    unfolding int_Idl by simp
  also have "... = {u. m dvd u} \<inter> {u. n dvd u}"
    using dvd_def[symmetric, of _ m]
    using dvd_def[symmetric, of _ n]
    using mult.commute[of m] mult.commute[of n]
    by algebra
  also have "... = {u. m dvd u \<and> n dvd u}" by blast
  also have "... = {u. lcm m n dvd u}" using lcm_least_iff[of m n] by blast
  also have "... = {u. \<exists>x. u = x * lcm m n}"
    using dvd_def[symmetric, of _ "lcm m n"]
    using mult.commute[of "lcm m n"]
    by algebra
  also have "... = Idl\<^bsub>\<Z>\<^esub> {lcm m n}" unfolding int_Idl by simp
  finally show ?thesis .
qed

corollary "coprime m n \<Longrightarrow> Idl\<^bsub>\<Z>\<^esub> {m} <+>\<^bsub>\<Z>\<^esub> Idl\<^bsub>\<Z>\<^esub> {n} = carrier \<Z>"
  using int_ideal_add coprime_imp_gcd_eq_1 int.genideal_one by simp

lemma genideal_uminus: "Idl\<^bsub>\<Z>\<^esub> {-x} = Idl\<^bsub>\<Z>\<^esub> {x}"
  unfolding int_Idl
  by (metis minus_mult_commute minus_mult_minus)

lemma genideal_normalize: "Idl\<^bsub>\<Z>\<^esub> {x} = Idl\<^bsub>\<Z>\<^esub> {normalize x}"
  apply (cases "x \<ge> 0")
  unfolding normalize_int_def using genideal_uminus by simp_all

corollary "coprime m n \<Longrightarrow> Idl\<^bsub>\<Z>\<^esub> {m} \<inter> Idl\<^bsub>\<Z>\<^esub> {n} = Idl\<^bsub>\<Z>\<^esub> {m * n}"
  using int_ideal_inter lcm_coprime genideal_normalize by metis

lemma int_ideal_inter_a_r_coset_distrib: "(Idl\<^bsub>\<Z>\<^esub> {m} \<inter> Idl\<^bsub>\<Z>\<^esub> {n}) +>\<^bsub>\<Z>\<^esub> x = (Idl\<^bsub>\<Z>\<^esub> {m} +>\<^bsub>\<Z>\<^esub> x) \<inter> (Idl\<^bsub>\<Z>\<^esub> {n} +>\<^bsub>\<Z>\<^esub> x)"
  by (auto simp add: a_r_coset_def r_coset_def)

lemma chinese_remainder_very_simple_int:
  fixes x y m n :: int
  assumes "x mod m = y mod m"
  assumes "x mod n = y mod n"
  shows "x mod (lcm m n) = y mod (lcm m n)"
proof -
  have "?thesis \<longleftrightarrow> Idl\<^bsub>\<Z>\<^esub> {lcm m n} +>\<^bsub>\<Z>\<^esub> x = Idl\<^bsub>\<Z>\<^esub> {lcm m n} +>\<^bsub>\<Z>\<^esub> y"
    using ZMod_def ZMod_eq_mod by algebra
  also have "... \<longleftrightarrow> (Idl\<^bsub>\<Z>\<^esub> {m} \<inter> Idl\<^bsub>\<Z>\<^esub> {n}) +>\<^bsub>\<Z>\<^esub> x = (Idl\<^bsub>\<Z>\<^esub> {m} \<inter> Idl\<^bsub>\<Z>\<^esub> {n}) +>\<^bsub>\<Z>\<^esub> y"
    using int_ideal_inter by presburger
  also have "... \<longleftrightarrow> (Idl\<^bsub>\<Z>\<^esub> {m} +>\<^bsub>\<Z>\<^esub> x) \<inter> (Idl\<^bsub>\<Z>\<^esub> {n} +>\<^bsub>\<Z>\<^esub> x) = (Idl\<^bsub>\<Z>\<^esub> {m} +>\<^bsub>\<Z>\<^esub> y) \<inter> (Idl\<^bsub>\<Z>\<^esub> {n} +>\<^bsub>\<Z>\<^esub> y)"
    by (simp only: int_ideal_inter_a_r_coset_distrib)
  also have "..." using assms ZMod_def ZMod_eq_mod by blast
  finally show ?thesis by blast
qed

lemma chinese_remainder_very_simple_nat:
  fixes x y m n :: nat
  assumes "x mod m = y mod m"
  assumes "x mod n = y mod n"
  shows "x mod (lcm m n) = y mod (lcm m n)"
  using assms chinese_remainder_very_simple_int
  by (meson lcm_unique_nat mod_eq_iff_dvd_symdiff_nat)

lemma special_residue_problem_unique_solution:
  fixes n :: nat
  fixes \<xi> \<eta> :: nat
  assumes "solves_special_residue_problem z1 n \<xi> \<eta>"
  assumes "solves_special_residue_problem z2 n \<xi> \<eta>"
  shows "z1 = z2"
proof -
  from assms have "z1 mod (lcm (int_lsbf_fermat.n n) (2 ^ (n + 2))) = z2 mod (lcm (int_lsbf_fermat.n n) (2 ^ (n + 2)))"
    unfolding solves_special_residue_problem_def
    using chinese_remainder_very_simple_nat by presburger
  moreover have "coprime (int_lsbf_fermat.n n) (2 ^ (n + 2))"
    using fn_zn_coprime .
  hence "lcm (int_lsbf_fermat.n n) (2 ^ (n + 2)) = (int_lsbf_fermat.n n) * (2 ^ (n + 2))"
    by (simp add: lcm_coprime)
  ultimately show "z1 = z2" using assms unfolding solves_special_residue_problem_def
    by (metis mod_less mult.commute)
qed

subsubsection "Subroutine for combining the final result"

fun combine_z_aux where
"combine_z_aux l acc [] = concat (rev acc)"
| "combine_z_aux l acc [z] = combine_z_aux l (z # acc) []"
| "combine_z_aux l acc (z1 # z2 # zs) = (let
    (z1h, z1t) = split_at l z1 in
    combine_z_aux l (z1h # acc) ((add_nat z1t z2) # zs)
  )"
(* called from the algorithm in order to add the z_j correctly.
  first argument: offset difference of z_(j+1) and z_j
  second argument: list of all z_j *)
definition combine_z :: "nat \<Rightarrow> nat_lsbf list \<Rightarrow> nat_lsbf" where
"combine_z l zs = combine_z_aux l [] zs"

lemma combine_z_aux_correct:
  assumes "l > 0"
  assumes "\<And>z. z \<in> set zs \<Longrightarrow> length z \<ge> l"
  shows "Nat_LSBF.to_nat (combine_z_aux l acc zs) = Nat_LSBF.to_nat (concat (rev acc)) +
    2 ^ (length (concat acc)) * (\<Sum>i \<leftarrow> [0..<length zs]. Nat_LSBF.to_nat (zs ! i) * 2 ^ (i * l))"
  using assms
proof (induction l acc zs rule: combine_z_aux.induct)
  case (1 l acc)
  then show ?case by simp
next
  case (2 l acc z)
  then show ?case by (simp add: to_nat_app)
next
  case (3 l acc z1 z2 zs)
  define z1h z1t where "z1h = take l z1" "z1t = drop l z1"
  have lena: "l \<le> length (add_nat z1t z2)"
    using length_add_nat_lower[of z1t z2] "3.prems" by force
  from z1h_z1t_def have "combine_z_aux l acc (z1 # z2 # zs) = combine_z_aux l (z1h # acc) ((add_nat z1t z2) # zs)"
    by simp
  then have "Nat_LSBF.to_nat (combine_z_aux l acc (z1 # z2 # zs)) = Nat_LSBF.to_nat ..." by argo
  also have "... = Nat_LSBF.to_nat (concat (rev (z1h # acc))) +
    2 ^ length (concat (z1h # acc)) *
    (\<Sum>i\<leftarrow>[0..<length (add_nat z1t z2 # zs)]. Nat_LSBF.to_nat ((add_nat z1t z2 # zs) ! i) * 2 ^ (i * l))"
    (is "... = ?t1 + ?p * ?t2")
    apply (intro "3.IH"[OF refl])
    subgoal unfolding split_at.simps using z1h_z1t_def by simp
    subgoal by (rule "3.prems")
    subgoal using "3.prems" lena by auto
    done
  also have "?t1 = Nat_LSBF.to_nat (concat (rev acc) @ z1h)"
    by simp
  also have "... = Nat_LSBF.to_nat (concat (rev acc)) + 2 ^ length (concat acc) * Nat_LSBF.to_nat z1h" (is "... = ?ta + ?tb")
    by (simp add: to_nat_app)
  also have "(?ta + ?tb) + ?p * ?t2 = ?ta + (?tb + ?p * ?t2)"
    by simp
  also have "?p = 2 ^ length (concat acc) * 2 ^ length z1h"
    by (simp add: power_add)
  also have "length z1h = l" using z1h_z1t_def "3.prems" by simp
  also have "?tb + (2 ^ length (concat acc) * 2 ^ l) * ?t2 = 2 ^ length (concat acc) * (Nat_LSBF.to_nat z1h + 2 ^ l *
    (\<Sum>i\<leftarrow>[0..<length (add_nat z1t z2 # zs)]. Nat_LSBF.to_nat ((add_nat z1t z2 # zs) ! i) * 2 ^ (i * l)))"
    (is "_ = _ * ?t3")
    by (simp add: add_mult_distrib2)
  also have "?t3 = Nat_LSBF.to_nat z1h +
    2 ^ l * (Nat_LSBF.to_nat (add_nat z1t z2) + (\<Sum>i\<leftarrow>[1..<Suc (length zs)]. Nat_LSBF.to_nat ((add_nat z1t z2 # zs) ! i) * 2 ^ (i * l)))"
    (is "_ = _ + _ * (_ + ?sum)")
    using sum_list_split_0[of "\<lambda>i. Nat_LSBF.to_nat ((add_nat z1t z2 # zs) ! i) * 2 ^ (i * l)" "length zs"] by simp
  also have "... = Nat_LSBF.to_nat z1h + 2 ^ l * Nat_LSBF.to_nat z1t + 2 ^ l * (Nat_LSBF.to_nat z2 + ?sum)"
    by (simp only: add_mult_distrib2 add_nat_correct)
  also have "... = Nat_LSBF.to_nat (z1h @ z1t) + 2 ^ l * (Nat_LSBF.to_nat z2 + ?sum)"
    by (simp add: to_nat_app \<open>length z1h = l\<close>)
  also have "... = Nat_LSBF.to_nat z1 + 2 ^ l * (Nat_LSBF.to_nat z2 + ?sum)"
    using z1h_z1t_def by simp
  also have "... = Nat_LSBF.to_nat z1 + 2 ^ l * (Nat_LSBF.to_nat z2 + (\<Sum>i\<leftarrow>[1..<Suc (length zs)]. Nat_LSBF.to_nat ((z2 # zs) ! i) * 2 ^ (i * l)))"
    apply (intro_cong "[cong_tag_2 (+), cong_tag_2 (*)]" more: refl sum_list_eq)
    subgoal premises prems for x
    proof -
      from prems obtain x' where "x = Suc x'"
        by (metis atLeastAtMost_iff atLeastAtMost_upt not0_implies_Suc not_one_le_zero)
      then show ?thesis by simp
    qed
    done
  also have "... = Nat_LSBF.to_nat z1 + 2 ^ l * (\<Sum>i \<leftarrow> [0..<Suc (length zs)]. Nat_LSBF.to_nat ((z2 # zs) ! i) * 2 ^ (i * l))"
    using sum_list_split_0[of "\<lambda>i. Nat_LSBF.to_nat ((z2 # zs) ! i) * 2 ^ (i * l)"] by simp
  also have "... = Nat_LSBF.to_nat z1 + (\<Sum>i \<leftarrow> [0..<Suc (length zs)]. 2 ^ l * (Nat_LSBF.to_nat ((z2 # zs) ! i) * 2 ^ (i * l)))"
    by (intro arg_cong2[where f = "(+)"] refl sum_list_const_mult[symmetric])
  also have "... = Nat_LSBF.to_nat z1 + (\<Sum>i \<leftarrow> [0..<Suc (length zs)]. Nat_LSBF.to_nat ((z2 # zs) ! i) * 2 ^ (Suc i * l))"
    apply (intro arg_cong2[where f = "(+)"] refl sum_list_eq)
    by (simp add: power_add)
  also have "... = Nat_LSBF.to_nat z1 + (\<Sum>i \<leftarrow> [0..<Suc (length zs)]. Nat_LSBF.to_nat ((z1 # z2 # zs) ! Suc i) * 2 ^ (Suc i * l))"
    by simp
  also have "... = Nat_LSBF.to_nat z1 + (\<Sum>i \<leftarrow> [1..<Suc (Suc (length zs))]. Nat_LSBF.to_nat ((z1 # z2 # zs) ! i) * 2 ^ (i * l))"
    unfolding sum_list_index_trafo[of "\<lambda>i. Nat_LSBF.to_nat ((z1 # z2 # zs) ! i) * 2 ^ (i * l)" Suc "[0..<Suc (length zs)]"]
    unfolding map_Suc_upt by simp
  also have "... = Nat_LSBF.to_nat ((z1 # z2 # zs) ! 0) * 2 ^ (0 * l) + (\<Sum>i \<leftarrow> [1..<length (z1 # z2 # zs)]. Nat_LSBF.to_nat ((z1 # z2 # zs) ! i) * 2 ^ (i * l))"
    by simp
  also have "... = (\<Sum>i \<leftarrow> [0..<length (z1 # z2 # zs)]. Nat_LSBF.to_nat ((z1 # z2 # zs) ! i) * 2 ^ (i * l))"
    using sum_list_split_0[where f = "\<lambda>i. Nat_LSBF.to_nat ((z1 # z2 # zs) ! i) * 2 ^ (i * l)"] by simp
  finally show ?case .
qed

lemma combine_z_correct:
  assumes "l > 0"
  assumes "\<And>z. z \<in> set zs \<Longrightarrow> length z \<ge> l"
  shows "Nat_LSBF.to_nat (combine_z l zs) = (\<Sum>i \<leftarrow> [0..<length zs]. Nat_LSBF.to_nat (zs ! i) * 2 ^ (i * l))"
  unfolding combine_z_def using combine_z_aux_correct[OF assms] by simp

lemma length_combine_z_aux_le:
  assumes "\<And>z. z \<in> set zs \<Longrightarrow> length z \<le> lz"
  assumes "length z \<le> lz + 1"
  assumes "l > 0"
  shows "length (combine_z_aux l acc (z # zs)) \<le> (lz + 1) * (length zs + 1) + length (concat acc)"
  using assms proof (induction zs arbitrary: acc z)
  case Nil
  then show ?case by simp
next
  case (Cons z1 zs)
  then have len_drop_z: "length (drop l z) \<le> lz" by simp
  have lena: "length (add_nat (drop l z) z1) \<le> lz + 1"
    apply (estimation estimate: length_add_nat_upper)
    using len_drop_z Cons.prems by simp
  have "length (combine_z_aux l acc (z # z1 # zs)) =
    length (combine_z_aux l (take l z # acc) (add_nat (drop l z) z1 # zs))"
    by simp
  also have "... \<le> (lz + 1) * (length zs + 1) + length (concat (take l z # acc))"
    apply (intro Cons.IH)
    subgoal using Cons.prems by simp
    subgoal using lena .
    subgoal using Cons.prems by simp
    done
  also have "... = (lz + 1) * (length (z1 # zs)) + length (take l z) + length (concat acc)"
    by simp
  also have "... \<le> (lz + 1) * length (z1 # zs) + (lz + 1) + length (concat acc)"
    apply (intro add_mono mult_le_mono order.refl)
    using Cons.prems by simp
  also have "... = (lz + 1) * (length (z1 # zs) + 1) + length (concat acc)"
    by simp
  finally show ?case .
qed

lemma length_combine_z_le:
  assumes "\<And>z. z \<in> set zs \<Longrightarrow> length z \<le> lz"
  assumes "l > 0"
  shows "length (combine_z l zs) \<le> (lz + 1) * length zs"
proof (cases zs)
  case Nil
  then show ?thesis by (simp add: combine_z_def)
next
  case (Cons z zs')
  have "length (combine_z l zs) \<le> (lz + 1) * (length zs' + 1) + length (concat ([] :: nat_lsbf list))"
    unfolding Cons combine_z_def
    apply (intro length_combine_z_aux_le)
    subgoal using assms Cons by simp
    subgoal using assms Cons by fastforce
    subgoal using assms by simp
    done
  also have "... = (lz + 1) * length zs"
    unfolding Cons by simp
  finally show ?thesis .
qed

subsection "Schoenhage-Strassen Multiplication in $\\mathbb{Z}_{F_m}$"

function schoenhage_strassen :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf" where
"schoenhage_strassen m a b =
  (if m < 3 then int_lsbf_fermat.from_nat_lsbf m (grid_mul_nat a b) else
  let
    n = (if odd m then (m + 1) div 2 else (m + 2) div 2);
    oe_n = (if odd m then n + 1 else n);
    a' = subdivide (2 ^ (n - 1)) a;
    b' = subdivide (2 ^ (n - 1)) b;

    \<comment> \<open>residue mod $2 ^ {n + 2}$\<close>
    \<alpha> = map (int_lsbf_mod.reduce (n + 2)) a';
    u = concat (map (fill (3*n + 5)) \<alpha>);
    \<beta> = map (int_lsbf_mod.reduce (n + 2)) b';
    v = concat (map (fill (3*n + 5)) \<beta>);
    uv = ensure_length ((3*n + 5) * 2 ^ (oe_n + 1)) (karatsuba_mul_nat u v);
    \<gamma> = subdivide (2 ^ (oe_n - 1)) (subdivide (3*n + 5) uv);
    \<eta> = map4 (\<lambda>x y z w.
        int_lsbf_mod.add_mod (n + 2)
        (int_lsbf_mod.subtract_mod (n + 2) (take (n + 2) x) (take (n + 2) y))
        (int_lsbf_mod.subtract_mod (n + 2) (take (n + 2) z) (take (n + 2) w))
      )
      (\<gamma> ! 0) (\<gamma> ! 1) (\<gamma> ! 2) (\<gamma> ! 3);

    \<comment> \<open>residue mod $F_n$\<close>
    prim_root_exponent = (if odd m then 1 else 2);
    a'_carrier = map (fill (2 ^ (n + 1))) a';
    b'_carrier = map (fill (2 ^ (n + 1))) b';
    a_dft = int_lsbf_fermat.fft n prim_root_exponent a'_carrier;
    b_dft = int_lsbf_fermat.fft n prim_root_exponent b'_carrier;
    a_dft_odds = evens_odds False a_dft;
    b_dft_odds = evens_odds False b_dft;
    c_dft_odds = map2 (schoenhage_strassen n) a_dft_odds b_dft_odds;
    c_diffs = int_lsbf_fermat.ifft n (prim_root_exponent * 2) c_dft_odds;
    \<xi>' = map2 (\<lambda>cj j. int_lsbf_fermat.add_fermat n
        (int_lsbf_fermat.divide_by_power_of_2 cj (oe_n + prim_root_exponent * j - 1))
        (int_lsbf_fermat.from_nat_lsbf n (replicate (oe_n + 2 ^ n) False @ [True])))
      c_diffs [0..<2 ^ (oe_n - 1)];
    \<xi> = map (int_lsbf_fermat.reduce n) \<xi>';

    \<comment> \<open>calculate $z_j$ for $j < 2 ^ n$\<close>
    z = map2 (solve_special_residue_problem n) \<xi> \<eta>;
    z_filled = map (fill (2 ^ (n - 1))) z;
    z_consts = replicate (2 ^ (oe_n - 1)) (replicate (oe_n + 2 ^ n) False @ [True]);
    z_sum = combine_z (2 ^ (n - 1)) (z_filled @ z_consts);
    result = int_lsbf_fermat.from_nat_lsbf m z_sum

  \<comment> \<open>return the resulting sum\<close>
  in result)"

  by pat_completeness auto

termination
  apply (relation "Wellfounded.measure (\<lambda>(n, a, b). n)")
  subgoal by blast
  by fastforce (* does not work with "subgoal"? *)

declare schoenhage_strassen.simps[simp del]

locale schoenhage_strassen_context =
  fixes m :: nat
  fixes a :: nat_lsbf
  fixes b :: nat_lsbf
  assumes m_ge_3: "\<not> m < 3"
  assumes a_carrier: "a \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  assumes b_carrier: "b \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
begin

sublocale m_lemmas
  using m_ge_3 by unfold_locales simp

sublocale A: carrier_input m a
  by unfold_locales (rule a_carrier)

sublocale B: carrier_input m b
  by unfold_locales (rule b_carrier)

definition uv_length where "uv_length = pad_length * 2 ^ (oe_n + 1)"
definition uv_unpadded where "uv_unpadded = karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad"
definition uv where "uv = ensure_length uv_length uv_unpadded"
definition \<gamma>s where "\<gamma>s = subdivide pad_length uv"
definition \<gamma> where "\<gamma> = subdivide (2 ^ (oe_n - 1)) \<gamma>s"
definition \<eta> where "\<eta> = map4 (\<lambda>x y z w. int_lsbf_mod.add_mod (n + 2)
        (int_lsbf_mod.subtract_mod (n + 2) (take (n + 2) x) (take (n + 2) y))
        (int_lsbf_mod.subtract_mod (n + 2) (take (n + 2) z) (take (n + 2) w))
      ) (\<gamma> ! 0) (\<gamma> ! 1) (\<gamma> ! 2) (\<gamma> ! 3)"
definition c_dft_odds where "c_dft_odds = map2 (schoenhage_strassen n) A.num_dft_odds B.num_dft_odds"
definition c_diffs where "c_diffs = int_lsbf_fermat.ifft n (prim_root_exponent * 2) c_dft_odds"
definition \<xi>' where "\<xi>' = map2 (\<lambda>cj j. int_lsbf_fermat.add_fermat n
        (int_lsbf_fermat.divide_by_power_of_2 cj (oe_n + prim_root_exponent * j - 1))
        (int_lsbf_fermat.from_nat_lsbf n (replicate (oe_n + 2 ^ n) False @ [True])))
      c_diffs [0..<2 ^ (oe_n - 1)]"
definition \<xi> where "\<xi> = map (int_lsbf_fermat.reduce n) \<xi>'"
definition z where "z = map2 (solve_special_residue_problem n) \<xi> \<eta>"
definition z_filled where "z_filled = map (fill (2 ^ (n - 1))) z"
definition z_consts where "z_consts = replicate (2 ^ (oe_n - 1)) (replicate (oe_n + 2 ^ n) False @ [True])"
definition z_sum where "z_sum = combine_z (2 ^ (n - 1)) (z_filled @ z_consts)"
definition result where "result = int_lsbf_fermat.from_nat_lsbf m z_sum"

lemmas defs = n_def oe_n_def A.defs B.defs pad_length_def uv_length_def uv_unpadded_def uv_def
    \<gamma>s_def \<gamma>_def \<eta>_def c_dft_odds_def c_diffs_def \<xi>'_def \<xi>_def z_def z_filled_def z_consts_def
    z_sum_def result_def prim_root_exponent_def \<mu>_def

lemma result_eq: "schoenhage_strassen m a b = result"
  unfolding schoenhage_strassen.simps[of m a b]
  unfolding iffD2[OF eq_False m_ge_3] if_False Let_def defs[symmetric]
  by (rule refl)

lemma length_uv: "length uv = uv_length"
  unfolding uv_def by (intro ensure_length_correct)

lemma pad_length_gt_0: "pad_length > 0" unfolding pad_length_def by simp

lemma scuv:
  "length (subdivide pad_length uv) = 2 ^ (oe_n + 1)"
  "x \<in> set (subdivide pad_length uv) \<Longrightarrow> length x = pad_length"
  using subdivide_correct[OF pad_length_gt_0] length_uv uv_length_def
  by auto

lemma length_c_dft_odds: "length c_dft_odds = 2 ^ (oe_n - 1)"
  unfolding c_dft_odds_def
  using A.length_num_dft_odds B.length_num_dft_odds by simp
lemma length_c_diffs: "length c_diffs = 2 ^ (oe_n - 1)"
  unfolding c_diffs_def
  by (intro Fnr.length_ifft length_c_dft_odds)
lemma length_\<xi>': "length \<xi>' = 2 ^ (oe_n - 1)"
  unfolding \<xi>'_def by (simp add: length_c_diffs)
lemma length_\<xi>: "length \<xi> = 2 ^ (oe_n - 1)"
  unfolding \<xi>_def by (simp add: length_\<xi>')

lemma \<gamma>_nth: "\<And>i j. i < 4 \<Longrightarrow> j < 2 ^ (oe_n - 1) \<Longrightarrow> \<gamma> ! i ! j = (subdivide pad_length uv) ! (i * 2 ^ (oe_n - 1) + j)"
  subgoal for i j
    unfolding \<gamma>_def \<gamma>s_def
    apply (intro nth_nth_subdivide[where k = 4])
    subgoal by simp
    subgoal
      apply (intro conjunct1[OF subdivide_correct])
      subgoal unfolding pad_length_def by simp
      subgoal using length_uv two_pow_Suc_oe_n_as_prod uv_length_def
        by simp
      done
    .
  done
lemma \<gamma>_nth': "\<And>j. j < 2 ^ (oe_n + 1) \<Longrightarrow> \<gamma> ! (j div 2 ^ (oe_n - 1)) ! (j mod 2 ^ (oe_n - 1)) = subdivide pad_length uv ! j"
  using index_decomp \<gamma>_nth by algebra
lemma sc\<gamma>: "length \<gamma> = 4" "\<And>i. i < 4 \<Longrightarrow> length (\<gamma> ! i) = 2 ^ (oe_n - 1)"
proof -
    have 1: "(2::nat) ^ (oe_n - 1) > 0" by simp
    have 2: "length (subdivide pad_length uv) = 2 ^ (oe_n - 1) * 4"
      using two_pow_Suc_oe_n_as_prod scuv(1) by simp
    show "length \<gamma> = 4" "\<And>i. i < 4 \<Longrightarrow> length (\<gamma> ! i) = 2 ^ (oe_n - 1)"
      using subdivide_correct[OF 1 2]
      unfolding \<gamma>_def[symmetric] \<gamma>s_def[symmetric] by simp_all
  qed
lemmas length_\<gamma> = sc\<gamma>(1)
lemmas length_\<gamma>_i = sc\<gamma>(2)
lemma length_\<gamma>_nth: "\<And>i j. i < 4 \<Longrightarrow> j < 2 ^ (oe_n - 1) \<Longrightarrow> length (\<gamma> ! i ! j) = pad_length"
  subgoal for i j
    using scuv \<gamma>_nth index_comp[of i j] by fastforce
  done
lemma length_\<eta>: "length \<eta> = 2 ^ (oe_n - 1)" unfolding \<eta>_def
  using length_\<gamma>_i by (simp add: map4_as_map)
    lemma length_z: "length z = 2 ^ (oe_n - 1)"
      unfolding z_def using length_\<xi> length_\<eta> by simp
lemma nth_z: "z ! j = solve_special_residue_problem n (\<xi> ! j) (\<eta> ! j)" if "j < 2 ^ (oe_n - 1)" for j
  unfolding z_def using length_z that length_\<xi> length_\<eta> by simp
lemma length_z_filled: "length z_filled = 2 ^ (oe_n - 1)"
  unfolding z_filled_def by (simp add: length_z)
lemma length_z_consts: "length z_consts = 2 ^ (oe_n - 1)"
  unfolding z_consts_def by simp

end

theorem schoenhage_strassen_correct':
  assumes "a \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  assumes "b \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  shows "int_lsbf_fermat.to_residue_ring m (schoenhage_strassen m a b)
      = int_lsbf_fermat.to_residue_ring m a \<otimes>\<^bsub>int_lsbf_fermat.Fn m\<^esub> int_lsbf_fermat.to_residue_ring m b \<and> schoenhage_strassen m a b \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  using assms
proof (induction m arbitrary: a b rule: less_induct)
  case (less m)
  then show ?case
  proof (cases "m < 3")
    case True
    then have def: "schoenhage_strassen m a b = int_lsbf_fermat.from_nat_lsbf m (grid_mul_nat a b)"
      by (simp add: schoenhage_strassen.simps)
    then have "int_lsbf_fermat.to_residue_ring m (schoenhage_strassen m a b)
      = int_lsbf_fermat.to_residue_ring m (grid_mul_nat a b)"
      using int_lsbf_fermat.from_nat_lsbf_correct by simp
    also have "... = int (Nat_LSBF.to_nat (grid_mul_nat a b)) mod int (2 ^ (2 ^ m) + 1)"
      unfolding int_lsbf_fermat.to_residue_ring.simps by argo
    also have "... = int (Nat_LSBF.to_nat a * Nat_LSBF.to_nat b) mod int (2 ^ (2 ^ m) + 1)"
      by (simp add: grid_mul_nat_correct)
    also have "... = int_lsbf_fermat.to_residue_ring m a \<otimes>\<^bsub>residue_ring (2 ^ (2 ^ m) + 1)\<^esub> int_lsbf_fermat.to_residue_ring m b"
      apply (simp add: residue_ring_def int_lsbf_fermat.to_residue_ring.simps)
      using mod_mult_eq
      by (metis add.commute)
    finally show ?thesis unfolding int_lsbf_fermat.Fn_def using def int_lsbf_fermat.from_nat_lsbf_correct(1)
      by (simp add: add.commute)
  next
    case False
    
    interpret schoenhage_strassen_context m a b
      using False "less.prems" by unfold_locales assumption+

    have Fn_def': "Fn = residue_ring (2 ^ 2 ^ n + 1)"
      unfolding Fn_def by (simp add: int_ops add.commute)
    have fn_Fn[simp]: "int_lsbf_fermat.Fn n = Fn"
      unfolding Fn_def int_lsbf_fermat.Fn_def by (rule refl)

    (* lengths, carriers etc. *)
    from Fmr.res_carrier_eq have Fm_carrierI: "\<And>i. 0 \<le> i \<Longrightarrow> i < 2 ^ 2 ^ m + 1 \<Longrightarrow> i \<in> carrier Fm"
      by simp

    define c' where "c' = map (\<lambda>j. \<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n))))) [0..<2 ^ oe_n]"
    define z' where "z' = (\<lambda>j. if j < 2 ^ (oe_n - 1) then c' ! j - c' ! (2 ^ (oe_n - 1) + j) + 2 ^ (oe_n + 2 ^ n) else 2 ^ (oe_n + 2 ^ n))"
    define z'' where "z'' = (\<lambda>j. if j < 2 ^ (oe_n - 1) then c' ! j \<ominus>\<^bsub>Fm\<^esub> c' ! (2 ^ (oe_n - 1) + j) \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) else 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n))"

    have length_c': "length c' = 2 ^ oe_n" unfolding c'_def by simp
    have c'_nth: "c' ! j = (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)))))"
      if "j < 2 ^ oe_n" for j
      unfolding c'_def using that by simp
    have c'_nth_nat: "c' ! j = int (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) * Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n))))"
      if "j < 2 ^ oe_n" for j
    proof -
      have "c' ! j = (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) * Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)))))"
        unfolding c'_nth[OF that] by simp
      also have "... = int (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) * Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)))"
        by (intro sum_list_int[symmetric])
      finally show "c' ! j = ..." .
    qed
    have c'_lower_bound: "c' ! j \<ge> 0" if "j < 2 ^ oe_n" for j
      unfolding c'_nth[OF that]
      apply (intro sum_list_nonneg) by fastforce
    have c'_upper_bound: "c' ! j < 2 ^ (oe_n + 2 ^ n)" if "j < 2 ^ oe_n" for j
    proof -
      have "Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) * Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)) < 2 ^ 2 ^ n"
        if "\<sigma> < 2 ^ oe_n" for \<sigma>
      proof -
        have "length (A.num_blocks ! \<sigma>) = 2 ^ (n - 1)" using A.length_nth_num_blocks that by simp
        then have "Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) < 2 ^ 2 ^ (n - 1)"
          using to_nat_length_bound by metis
        moreover have "length (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)) = 2 ^ (n - 1)"
          using B.length_nth_num_blocks by simp
        then have "Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)) < 2 ^ 2 ^ (n - 1)"
          using to_nat_length_bound by metis
        ultimately have "Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) * Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)) <
          2 ^ 2 ^ (n - 1) * 2 ^ 2 ^ (n - 1)"
          by (intro mult_strict_mono) simp_all
        also have "... = 2 ^ 2 ^ n" using n_gt_1
          by (simp add: power_add[symmetric] mult_2[symmetric] power_Suc[symmetric])
        finally show ?thesis .
      qed
      then have "(\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>) * Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n)))) < length [0..<2 ^ oe_n] * 2 ^ 2 ^ n"
        by (intro sum_list_estimation_le) simp_all
      then have "c' ! j < length [0..<2 ^ oe_n] * 2 ^ 2 ^ n"
        unfolding c'_nth_nat[OF that]
        using nat_int_comparison(2)[symmetric] by blast
      also have "... = 2 ^ (oe_n + 2 ^ n)"
        by (simp add: power_add)
      finally show "c' ! j < 2 ^ (oe_n + 2 ^ n)" .
    qed
    have c'_carrier: "c' ! j \<in> carrier Fm" if "j < 2 ^ oe_n" for j
    proof -
      have "c' ! j < 2 ^ (oe_n + 2 ^ n)" using c'_upper_bound[OF that] .
      also have "... < 2 ^ (oe_n + 1 + 2 ^ n)" by simp
      also have "... \<le> 2 ^ 2 ^ m" using iffD2[OF zle_int two_pow_oe_n_m_bound_1] by simp
      finally show ?thesis
        by (simp add: Fm_def residue_ring_def c'_lower_bound[OF that])
    qed
    have c'_alt: "c' ! j = (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. \<Sum>\<rho> \<leftarrow> [0..<2 ^ oe_n]. of_bool ([j = \<sigma> + \<rho>] (mod 2 ^ oe_n)) * (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_blocks ! \<rho>))))"
      if "j < 2 ^ oe_n" for j
    proof -
      have "c' ! j = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) *
                int (Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n))))"
        using c'_nth[OF that] .
      also have "... = (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. \<Sum>\<rho> \<leftarrow> [0..<2 ^ oe_n]. of_bool (\<rho> = (2 ^ oe_n + j - \<sigma>) mod 2 ^ oe_n) * (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_blocks ! \<rho>))))"
        by (intro semiring_1_sum_list_eq of_bool_distinct_in[symmetric]) simp_all
      also have "... = (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. \<Sum>\<rho> \<leftarrow> [0..<2 ^ oe_n]. of_bool ([j = \<sigma> + \<rho>] (mod 2 ^ oe_n)) * (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_blocks ! \<rho>))))"
        apply (intro_cong "[cong_tag_2 (*), cong_tag_1 of_bool]" more: semiring_1_sum_list_eq refl)
        subgoal premises prems for \<sigma> \<rho>
          unfolding cong_def
          using cyclic_index_lemma[of \<sigma> "2 ^ oe_n" \<rho> j, symmetric] that prems
          by auto
        done
      finally show ?thesis .
    qed

    have z'_z'': "z' j = z'' j" if "j < 2 ^ oe_n" for j
    proof -
      have "(2 :: int) ^ (oe_n + 2 ^ n) = int (2 ^ (oe_n + 2 ^ n))" by simp
      also have "... = int (2 ^ (oe_n + 2 ^ n) mod Fmr.n)"
        apply (intro arg_cong[where f = int] mod_less[symmetric])
        using oe_n_m_bound_0
        by (meson one_less_numeral_iff power_strict_increasing semiring_norm(76) trans_less_add1)
      also have "... = 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)"
        by (simp add: Fmr.pow_nat_eq zmod_int)
      finally have twopow: "(2 :: int) ^ (oe_n + 2 ^ n) = 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)" .
      show "z' j = z'' j"
      proof (cases "j < 2 ^ (oe_n - 1)")
        case True
        then have "z' j = c' ! j - c' ! (2 ^ (oe_n - 1) + j) + 2 ^ (oe_n + 2 ^ n)"
          unfolding z'_def by simp
        moreover have "... \<ge> 0" "... < Fmr.n"
          subgoal using c'_upper_bound[of "2 ^ (oe_n - 1) + j"] c'_lower_bound[of j]
            using \<open>j < 2 ^ oe_n\<close> index_intros(2)[of j] True by simp
          subgoal
          proof -
            have "c' ! j - c' ! (2 ^ (oe_n - 1) + j) < 2 ^ (oe_n + 2 ^ n)"
              using c'_upper_bound[OF \<open>j < 2 ^ oe_n\<close>] c'_lower_bound[OF index_intros(2)[OF \<open>j < 2 ^ (oe_n - 1)\<close>]]
              by simp
            then have "c' ! j - c' ! (2 ^ (oe_n - 1) + j) + 2 ^ (oe_n + 2 ^ n) < 2 ^ (oe_n + 1 + 2 ^ n)"
              by simp
            also have "... < 2 ^ 2 ^ m + 1"
              using two_pow_oe_n_m_bound_1 by simp
            finally show ?thesis by simp
          qed
          done
        ultimately have "z' j = z' j mod Fmr.n" by simp
        have "z'' j = c' ! j \<ominus>\<^bsub>Fm\<^esub> c' ! (2 ^ (oe_n - 1) + j) \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)"
          unfolding z''_def using True by simp
        also have "... = ((c' ! j \<ominus>\<^bsub>Fm\<^esub> c' ! (2 ^ (oe_n - 1) + j)) + 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) mod Fmr.n"
          by (intro Fmr.res_add_eq)
        also have "... = ((c' ! j \<ominus>\<^bsub>Fm\<^esub> c' ! (2 ^ (oe_n - 1) + j)) + 2 ^ (oe_n + 2 ^ n)) mod Fmr.n"
          using \<open>2 ^ (oe_n + 2 ^ n) = 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)\<close> by argo
        also have "... = ((c' ! j - c' ! (2 ^ (oe_n - 1) + j)) mod Fmr.n + 2 ^ (oe_n + 2 ^ n)) mod Fmr.n"
          using Fmr.residues_minus_eq by simp
        also have "... = ((c' ! j - c' ! (2 ^ (oe_n - 1) + j)) + 2 ^ (oe_n + 2 ^ n)) mod Fmr.n"
          by (simp add: mod_add_left_eq)
        also have "... = z' j mod Fmr.n"
          unfolding \<open>z' j = c' ! j - c' ! (2 ^ (oe_n - 1) + j) + 2 ^ (oe_n + 2 ^ n)\<close> by (intro refl)
        finally show ?thesis using \<open>z' j = z' j mod Fmr.n\<close> by argo
      next
        case False
        then show ?thesis unfolding z'_def z''_def using twopow by simp
      qed
    qed

    have z'_carrier: "z'' j \<in> carrier Fm" if "j < 2 ^ oe_n" for j
      unfolding z''_def
      apply (intro prop_ifI[where P = "\<lambda>p. p \<in> carrier Fm"] Fmr.a_closed Fmr.minus_closed Fmr.nat_pow_closed c'_carrier Fmr.two_in_carrier)
      using index_intros by simp_all

    have "Fmr.to_residue_ring a \<otimes>\<^bsub>Fm\<^esub> Fmr.to_residue_ring b =
      (\<Oplus>\<^bsub>Fm\<^esub>j \<leftarrow> [0..<2 ^ oe_n]. (\<Oplus>\<^bsub>Fm\<^esub>k \<leftarrow> [0..<2 ^ oe_n].
      map (int \<circ> Nat_LSBF.to_nat) A.num_blocks ! k \<otimes>\<^bsub>Fm\<^esub> map (int \<circ> Nat_LSBF.to_nat) B.num_blocks ! ((2 ^ oe_n + j - k) mod 2 ^ oe_n)) \<otimes>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> (2::nat) ^ (n - 1)) [^]\<^bsub>Fm\<^esub> j))"
      unfolding A.to_res_num B.to_res_num
      apply (intro Fmr.root_of_unity_power_sum_product)
      apply (intro Fmr.root_of_unity_power_sum_product two_pow_oe_n_root_of_unity_Fm A.num_blocks_carrier_Fm)
      subgoal for j using A.num_blocks_carrier_Fm[of j] A.length_num_blocks by simp
      subgoal for j using B.num_blocks_carrier_Fm[of j] B.length_num_blocks by simp
      done
    also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (c' ! i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
      apply (intro Fmr.monoid_sum_list_cong arg_cong2[where f = "(\<otimes>\<^bsub>Fm\<^esub>)"])
      subgoal premises prems for j
      proof -
        from prems have "j < 2 ^ oe_n" by simp
        have "(\<Oplus>\<^bsub>Fm\<^esub>k \<leftarrow> [0..<2 ^ oe_n]. map (int \<circ> Nat_LSBF.to_nat) A.num_blocks ! k \<otimes>\<^bsub>Fm\<^esub>
          map (int \<circ> Nat_LSBF.to_nat) B.num_blocks ! ((2 ^ oe_n + j - k) mod 2 ^ oe_n)) = 
            (\<Oplus>\<^bsub>Fm\<^esub>k \<leftarrow> [0..<2 ^ oe_n]. (map (int \<circ> Nat_LSBF.to_nat) A.num_blocks ! k *
          map (int \<circ> Nat_LSBF.to_nat) B.num_blocks ! ((2 ^ oe_n + j - k) mod 2 ^ oe_n)) mod Fmr.n)"
          by (intro Fmr.monoid_sum_list_cong Fmr.res_mult_eq)
        also have "... = (\<Sum>k \<leftarrow> [0..<2 ^ oe_n]. (map (int \<circ> Nat_LSBF.to_nat) A.num_blocks ! k *
          map (int \<circ> Nat_LSBF.to_nat) B.num_blocks ! ((2 ^ oe_n + j - k) mod 2 ^ oe_n))) mod Fmr.n"
          by (intro Fmr.monoid_sum_list_eq_sum_list')
        also have "... = c' ! j mod Fmr.n"
          unfolding c'_nth[OF \<open>j < 2 ^ oe_n\<close>]
          apply (intro_cong "[cong_tag_2 (mod)]" more: refl semiring_1_sum_list_eq)
          using A.length_num_blocks B.length_num_blocks by simp_all
        also have "... = c' ! j"
          using Fmr.carrier_mod_eq[OF c'_carrier[OF \<open>j < 2 ^ oe_n\<close>]] .
        finally show ?thesis .
      qed
      subgoal for j unfolding Fmr.nat_pow_pow[OF Fmr.two_in_carrier]
        by (intro arg_cong2[where f = "([^]\<^bsub>Fm\<^esub>)"] refl mult.commute)
      done
    also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (z' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
    proof -
      have "(\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (z' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))) =
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (z'' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro_cong "[cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>)]" more: Fmr.monoid_sum_list_cong refl)
        using z'_z'' by simp
      also have "... =
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. (z'' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))) \<oplus>\<^bsub>Fm\<^esub>
        2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ (oe_n - 1) * 2 ^ (n - 1)) \<otimes>\<^bsub>Fm\<^esub> (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. (z'' (2 ^ (oe_n - 1) + i)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro Fmr.monoid_pow_sum_split two_pow_oe_n_as_halves[symmetric] z'_carrier Fmr.two_in_carrier)
        by assumption
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. (c' ! i \<ominus>\<^bsub>Fm\<^esub> c' ! (2 ^ (oe_n - 1) + i) \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))) \<oplus>\<^bsub>Fm\<^esub>
        2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ (oe_n - 1) * 2 ^ (n - 1)) \<otimes>\<^bsub>Fm\<^esub> (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>)]" more: Fmr.monoid_sum_list_cong refl)
        by (simp_all add: z''_def)
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! i \<ominus>\<^bsub>Fm\<^esub> c' ! (2 ^ (oe_n - 1) + i) \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>), cong_tag_2 ([^]\<^bsub>Fm\<^esub>)]" more: refl)
        using two_pow_m0_as_prod by simp
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! i \<ominus>\<^bsub>Fm\<^esub> (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n))) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>)]" more: refl Fmr.monoid_sum_list_cong Fmr.diff_diff[symmetric] Fmr.nat_pow_closed c'_carrier Fmr.two_in_carrier)
        using index_intros by simp_all
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<ominus>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>)]" more: refl Fmr.monoid_pow_sum_diff'[symmetric] Fmr.minus_closed Fmr.nat_pow_closed c'_carrier Fmr.two_in_carrier)
        using index_intros by simp_all
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> (\<ominus>\<^bsub>Fm\<^esub> \<one>\<^bsub>Fm\<^esub>) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>)]" more: refl Fmr.diff_eq_add_mult_one Fmr.monoid_sum_list_closed Fmr.m_closed Fmr.nat_pow_closed Fmr.minus_closed c'_carrier Fmr.two_in_carrier)
        using index_intros by simp_all
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> (2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m)) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        using Fmr.two_pow_half_carrier_length_residue_ring by argo
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m)) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))))"
        apply (intro Fmr.a_assoc Fmr.m_closed Fmr.nat_pow_closed Fmr.monoid_sum_list_closed Fmr.minus_closed c'_carrier Fmr.two_in_carrier)
        using index_intros by simp_all
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m)) \<otimes>\<^bsub>Fm\<^esub>
        ((\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> 
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>)]" more: refl Fmr.r_distr[symmetric] Fmr.monoid_sum_list_closed Fmr.m_closed Fmr.nat_pow_closed c'_carrier Fmr.two_in_carrier Fmr.minus_closed)
        using index_intros by simp
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m)) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i) \<ominus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n) \<oplus>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (oe_n + 2 ^ n)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>)]" more: refl Fmr.monoid_pow_sum_add' Fmr.minus_closed Fmr.nat_pow_closed c'_carrier Fmr.two_in_carrier)
        using index_intros by simp
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ m)) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))))"
        apply (intro_cong "[cong_tag_2 (\<oplus>\<^bsub>Fm\<^esub>), cong_tag_2 (\<otimes>\<^bsub>Fm\<^esub>)]" more: refl Fmr.monoid_sum_list_cong Fmr.minus_cancel Fmr.nat_pow_closed c'_carrier Fmr.two_in_carrier)
        using index_intros by simp
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))
        \<oplus>\<^bsub>Fm\<^esub> ((2 [^]\<^bsub>Fm\<^esub> ((2::nat) ^ (oe_n - 1) * 2 ^ (n - 1))) \<otimes>\<^bsub>Fm\<^esub>
        (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ (oe_n - 1)].
          (c' ! (2 ^ (oe_n - 1) + i)) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))))"
        using two_pow_m0_as_prod by (simp add: mult.commute)
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. c' ! i \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro Fmr.monoid_pow_sum_split[symmetric] two_pow_oe_n_as_halves[symmetric] c'_carrier Fmr.two_in_carrier)
        by assumption
      finally show ?thesis by argo
    qed
    finally have result0: "Fmr.to_residue_ring a \<otimes>\<^bsub>Fm\<^esub> Fmr.to_residue_ring b
      = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (z' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))" .


    (* goal 1: \<eta> contains the residues of z_j mod 2 ^ (n + 2) *)
    have "Nat_LSBF.to_nat uv = Nat_LSBF.to_nat A.num_Zn_pad * Nat_LSBF.to_nat B.num_Zn_pad"
    proof (cases "length (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad) \<le> uv_length")
      case True
      have "uv = fill uv_length (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad)"
        unfolding uv_def ensure_length_def uv_unpadded_def
        apply (intro take_id)
        using True unfolding length_fill' by linarith
      then have "Nat_LSBF.to_nat uv = Nat_LSBF.to_nat (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad)" by simp
      also have "... = Nat_LSBF.to_nat A.num_Zn_pad * Nat_LSBF.to_nat B.num_Zn_pad" by (rule karatsuba_mul_nat_correct)
      finally show ?thesis .
    next
      case False
      define uv' where "uv' = take uv_length (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad)"
      define f where "f = drop uv_length (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad)"
      have "karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad = uv' @ f"
        unfolding uv'_def f_def
        by (rule append_take_drop_id[symmetric])
      from uv'_def False have "length uv' = uv_length"
        unfolding uv'_def length_take using False
        by (intro min.absorb2) linarith
      have "f = replicate (length f) False"
      proof (rule ccontr)
        assume "f \<noteq> replicate (length f) False"
        with list_is_replicate_iff obtain i where "i < length f" "f ! i = True" by force
        define j where "j = uv_length + i"
        then have "karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad ! j = True"
          using \<open>karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad = uv' @ f\<close> \<open>length uv' = uv_length\<close>
          using \<open>f ! i = True\<close> by (metis nth_append_length_plus)
        then have "Nat_LSBF.to_nat (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad) \<ge> 2 ^ j"
          apply (intro to_nat_nth_True_bound)
          subgoal using j_def \<open>i < length f\<close> \<open>length uv' = uv_length\<close>
            using \<open>karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad = uv' @ f\<close> by simp
          subgoal .
          done
        moreover have "(2::nat) ^ j \<ge> 2 ^ uv_length"
          apply (intro power_increasing) using j_def by simp_all
        ultimately have G: "Nat_LSBF.to_nat (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad) \<ge> 2 ^ uv_length"
          by linarith
        have "Nat_LSBF.to_nat (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad) = Nat_LSBF.to_nat A.num_Zn_pad * Nat_LSBF.to_nat B.num_Zn_pad"
          by (intro karatsuba_mul_nat_correct)
        also have "... < 2 ^ length A.num_Zn_pad * 2 ^ length B.num_Zn_pad"
          by (intro mult_strict_mono to_nat_length_bound) simp_all
        also have "... = 2 ^ (length A.num_Zn_pad + length B.num_Zn_pad)"
          by (simp only: power_add)
        also have "... = 2 ^ (pad_length * 2 ^ oe_n + pad_length * 2 ^ oe_n)"
          using A.length_num_Zn_pad B.length_num_Zn_pad
          by simp
        also have "... = 2 ^ uv_length"
          unfolding uv_length_def
          by (intro arg_cong[where f = "power 2"]) simp
        finally show "False" using G by linarith
      qed
      then have "Nat_LSBF.to_nat (karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad) = Nat_LSBF.to_nat uv'"
        using \<open>karatsuba_mul_nat A.num_Zn_pad B.num_Zn_pad = uv' @ f\<close>
        using to_nat_app_replicate by metis
      moreover have "uv' = uv"
        unfolding uv'_def uv_def ensure_length_def uv_unpadded_def
        apply (intro arg_cong2[where f = take] refl fill_id[symmetric])
        using False by linarith
      ultimately show ?thesis unfolding karatsuba_mul_nat_correct by simp
    qed

    define \<gamma>' where "\<gamma>' \<equiv> \<lambda>\<tau>. (\<Sum>\<sigma> \<leftarrow> [0..<2 ^ oe_n]. \<Sum>\<rho> \<leftarrow> [0..<2 ^ oe_n]. of_bool (\<tau> = \<sigma> + \<rho>) * (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>) * Nat_LSBF.to_nat (B.num_Zn ! \<rho>)))"

    have to_nat_\<gamma>: "Nat_LSBF.to_nat (\<gamma> ! i ! j) = \<gamma>' (i * 2 ^ (oe_n - 1) + j)"
      if "i < 4" "j < 2 ^ (oe_n - 1)" for i j
    proof -
      have "Nat_LSBF.to_nat uv = (\<Sum>j \<leftarrow> [0..<2 ^ (oe_n + 1)]. Nat_LSBF.to_nat (subdivide pad_length uv ! j) * 2 ^ (j * pad_length))"
        apply (intro to_nat_subdivide pad_length_gt_0)
        unfolding length_uv uv_length_def by (rule refl)
      also have "... = (\<Sum>j \<leftarrow> [0..<2 ^ (oe_n + 1)].
          Nat_LSBF.to_nat (\<gamma> ! (j div 2 ^ (oe_n - 1)) ! (j mod 2 ^ (oe_n - 1)))
          * 2 ^ (j * pad_length))"
        apply (intro_cong "[cong_tag_2 (*), cong_tag_1 Nat_LSBF.to_nat]" more: semiring_1_sum_list_eq refl)
        apply (intro \<gamma>_nth'[symmetric]) by simp
      finally have 1: "Nat_LSBF.to_nat uv = ..." .

      let ?exp = "\<lambda>i. 2 ^ (i * pad_length)"
      let ?a = "\<lambda>i. Nat_LSBF.to_nat (A.num_Zn ! i)"
      let ?b = "\<lambda>i. Nat_LSBF.to_nat (B.num_Zn ! i)"
      from A.to_nat_num_Zn_pad B.to_nat_num_Zn_pad
      have "Nat_LSBF.to_nat uv =
        (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. ?a i * ?exp i) *
        (\<Sum>j \<leftarrow> [0..<2 ^ oe_n]. ?b j * ?exp j)"
        using \<open>Nat_LSBF.to_nat uv = Nat_LSBF.to_nat A.num_Zn_pad * Nat_LSBF.to_nat B.num_Zn_pad\<close>
        by argo
      also have "... = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. \<Sum>j \<leftarrow> [0..<2 ^ oe_n]. (?a i * ?exp i) * (?b j * ?exp j))"
        by (rule sum_list_mult_sum_list)
      also have "... = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. \<Sum>j \<leftarrow> [0..<2 ^ oe_n]. (?a i * ?b j) * ?exp (i + j))"
        by (intro sum_list_eq; simp add: algebra_simps power_add)
      also have "... = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. \<Sum>j \<leftarrow> [0..<2 ^ oe_n]. \<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1) - 1].
        of_bool (k = i + j) * ((?a i * ?b j) * ?exp (i + j)))"
        by (intro sum_list_eq of_bool_distinct_in[symmetric]; simp)
      also have "... = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. \<Sum>j \<leftarrow> [0..<2 ^ oe_n]. \<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1) - 1].
        of_bool (k = i + j) * ((?a i * ?b j) * ?exp k))"
        by (intro sum_list_eq[where xs = "[0..<2 ^ oe_n]"] of_bool_var_swap[symmetric])
      also have "... = (\<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1) - 1]. \<Sum>i \<leftarrow> [0..<2 ^ oe_n]. \<Sum>j \<leftarrow> [0..<2 ^ oe_n].
        of_bool (k = i + j) * ((?a i * ?b j) * ?exp k))"
        by (simp only: sum_swap[where ys = "[0..<2 ^ (oe_n + 1) - 1]"])
      also have "... = (\<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1) - 1]. \<gamma>' k * ?exp k)"
        apply (unfold \<gamma>'_def)
        apply (intro sum_list_eq)
        apply (unfold sum_list_mult_const[symmetric])
        apply (intro sum_list_eq)
        apply (simp only: algebra_simps)
        done
      also have "... = (\<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1)]. \<gamma>' k * 2 ^ (k * pad_length))"
      proof -
        have "(\<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1)]. \<gamma>' k * 2 ^ (k * pad_length)) =
          (\<Sum>k \<leftarrow> [0..<2 ^ (oe_n + 1) - 1]. \<gamma>' k * 2 ^ (k * pad_length)) + \<gamma>' (2 ^ (oe_n + 1) - 1) * 2 ^ ((2 ^ (oe_n + 1) - 1) * pad_length)"
          apply (intro sum_list_split_Suc) by simp
        also have "\<gamma>' (2 ^ (oe_n + 1) - 1) = (\<Sum>i \<leftarrow> [0..<2 ^ oe_n]. \<Sum>j \<leftarrow> [0..<2 ^ oe_n]. 0)"
          unfolding \<gamma>'_def
        proof (intro semiring_1_sum_list_eq)
          fix i j :: nat
          assume "i \<in> set [0..<2 ^ oe_n]" "j \<in> set [0..<2 ^ oe_n]"
          then have "i + j \<le> (2 ^ oe_n - 1) + (2 ^ oe_n - 1)" by simp
          also have "... = 2 ^ (oe_n + 1) - 2" by simp
          also have "... < 2 ^ (oe_n + 1) - 1" using oe_n_gt_0
            by (meson diff_less_mono2 one_less_numeral_iff one_less_power pos_add_strict semiring_norm(76) zero_less_one)
          finally have "2 ^ (oe_n + 1) - 1 \<noteq> i + j" by simp
          then have "of_bool (2 ^ (oe_n + 1) - 1 = i + j) = 0" by simp
          then show "of_bool (2 ^ (oe_n + 1) - 1 = i + j) * (Nat_LSBF.to_nat (A.num_Zn ! i) * Nat_LSBF.to_nat (B.num_Zn ! j)) = 0"
            using mult_zero_left by metis
        qed
        also have "... = 0" by simp
        finally show ?thesis by simp
      qed
      finally have "Nat_LSBF.to_nat uv = ..." .
      with 1 have 2: "(\<Sum>j \<leftarrow> [0..<2 ^ (oe_n + 1)].
          Nat_LSBF.to_nat (\<gamma> ! (j div 2 ^ (oe_n - 1)) ! (j mod 2 ^ (oe_n - 1)))
          * 2 ^ (j * pad_length)) = ..." by argo
      have "\<And>j. j < 2 ^ (oe_n + 1) \<Longrightarrow>
        Nat_LSBF.to_nat (\<gamma> ! (j div 2 ^ (oe_n - 1)) ! (j mod 2 ^ (oe_n - 1))) = \<gamma>' j"
        apply (intro power_sum_nat_eq[where n = "2 ^ (oe_n + 1)" and g = \<gamma>' and x = 2 and c = pad_length])
        subgoal by simp
        subgoal by (rule pad_length_gt_0)
        subgoal for i j
        proof -
          assume "j < 2 ^ (oe_n + 1)"
          then have "Nat_LSBF.to_nat (\<gamma> ! (j div 2 ^ (oe_n - 1)) ! (j mod 2 ^ (oe_n - 1))) = Nat_LSBF.to_nat (subdivide pad_length uv ! j)"
            apply (intro arg_cong[where f = Nat_LSBF.to_nat] \<gamma>_nth') .
          also have "... < 2 ^ (length (subdivide pad_length uv ! j))"
            by (intro to_nat_length_bound)
          also have "... = 2 ^ pad_length"
            apply (intro arg_cong[where f = "power 2"] scuv(2) nth_mem)
            using \<open>j < 2 ^ (oe_n + 1)\<close> scuv(1) by argo
          finally show "Nat_LSBF.to_nat (\<gamma> ! (j div 2 ^ (oe_n - 1)) ! (j mod 2 ^ (oe_n - 1))) < 2 ^ pad_length" .
        qed
        subgoal for i j
        proof -
          have "\<gamma>' j = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n]. of_bool (j = \<sigma> + \<rho>) * (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>) * Nat_LSBF.to_nat (B.num_Zn ! \<rho>)))"
            unfolding \<gamma>'_def by argo
          also have "... \<le> (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n]. of_bool (j = \<sigma> + \<rho>) * ((2 ^ (n + 2) - 1) * (2 ^ (n + 2) - 1)))"
            apply (intro sum_list_mono mult_le_mono2 mult_le_mono)
            subgoal for \<sigma> \<rho> unfolding A.num_Zn_def
              using A.length_num_blocks to_nat_length_upper_bound[of "map Znr.reduce A.num_blocks ! \<sigma>"] Znr.length_reduce
              by simp
            subgoal for \<sigma> \<rho> unfolding B.num_Zn_def
              using B.length_num_blocks to_nat_length_upper_bound[of "map Znr.reduce B.num_blocks ! \<rho>"] Znr.length_reduce
              by simp
            done
          also have "... = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n]. of_bool (j = \<sigma> + \<rho>)) * ((2 ^ (n + 2) - 1) * (2 ^ (n + 2) - 1))"
            by (simp add: sum_list_mult_const)
          also have "... \<le> (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. 1) * ((2 ^ (n + 2) - 1) * (2 ^ (n + 2) - 1))"
            apply (intro mult_le_mono1 sum_list_mono)
            subgoal for \<sigma>
              by (intro of_bool_sum_leq_1) simp_all
            done
          also have "... = 2 ^ oe_n * ((2 ^ (n + 2) - 1) * (2 ^ (n + 2) - 1))"
            apply (intro arg_cong2[where f =  "(*)"] refl)
            using sum_list_triv[of "(1::nat)" "[0..<2 ^ oe_n]"] by simp
          also have "... < 2 ^ oe_n * (2 ^ (n + 2) * 2 ^ (n + 2))"
            apply (intro iffD2[OF mult_less_cancel1] conjI)
            subgoal by simp
            subgoal by (intro mult_strict_mono) simp_all
            done
          also have "... = 2 ^ (oe_n + 2 * n + 4)" by (simp add: power_add power2_eq_square power_even_eq)
          finally show ?thesis unfolding oe_n_def apply (cases "odd m")
            subgoal by (simp add: add.commute pad_length_def)
            subgoal by (simp add: power_add pad_length_def)
            done
        qed
        subgoal for j using 2 .
        subgoal by assumption
        done
      then show "Nat_LSBF.to_nat (\<gamma> ! i ! j) = \<gamma>' (i * 2 ^ (oe_n - 1) + j)"
        using index_comp that by metis
    qed
    have \<gamma>c: "[int (\<gamma>' \<tau>) + int (\<gamma>' (2 ^ oe_n + \<tau>)) = c' ! \<tau>] (mod 2 ^ (n + 2))"
      if "\<tau> < 2 ^ oe_n" for \<tau>
    proof -
      have "c' ! \<tau> mod 2 ^ (n + 2) = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          of_bool [\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n) *
         (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_blocks ! \<rho>)))) mod 2 ^ (n + 2)"
        by (intro arg_cong[where f = "\<lambda>j. j mod _"] c'_alt[OF that])
      also have "... = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          (of_bool [\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n) *
         ((int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) mod 2 ^ (n + 2)) * (int (Nat_LSBF.to_nat (B.num_blocks ! \<rho>)) mod 2 ^ (n + 2))))) mod 2 ^ (n + 2)"
        apply (intro sum_list_mod')
        using mod_mult_right_eq[of "of_bool _"] mod_mult_eq[of "int (Nat_LSBF.to_nat (A.num_blocks ! _))" _ "int (Nat_LSBF.to_nat (B.num_blocks ! _))"]
        by metis
      also have "(\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          (of_bool [\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n) *
         ((int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) mod 2 ^ (n + 2)) * (int (Nat_LSBF.to_nat (B.num_blocks ! \<rho>)) mod 2 ^ (n + 2))))) =
        (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          (of_bool [\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n) *
         ((int (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>))) * (int (Nat_LSBF.to_nat (B.num_Zn ! \<rho>))))))"
        apply (intro_cong "[cong_tag_2 (*)]" more: semiring_1_sum_list_eq refl)
        unfolding A.num_Zn_def B.num_Zn_def
        subgoal for \<sigma> \<rho>
          using A.length_num_blocks
          using Znr.to_nat_reduce
          by (simp add: zmod_int)
        subgoal for \<sigma> \<rho>
          using B.length_num_blocks Znr.to_nat_reduce
          by (simp add: zmod_int)
        done
      also have "... = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          of_bool (\<tau> = \<sigma> + \<rho> \<or> \<tau> + 2 ^ oe_n = \<sigma> + \<rho>) *
         (int (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_Zn ! \<rho>))))"
        proof (intro_cong "[cong_tag_2 (*), cong_tag_1 of_bool]" more: semiring_1_sum_list_eq refl)
          fix \<sigma> \<rho> :: nat
          assume a: "\<sigma> \<in> set [0..<2 ^ oe_n]" "\<rho> \<in> set [0..<2 ^ oe_n]"
          have "[\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n) \<Longrightarrow> \<tau> = \<sigma> + \<rho> \<or> \<tau> + 2 ^ oe_n = \<sigma> + \<rho>"
          proof -
            assume "[\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n)"
            then have "\<tau> mod (2 ^ oe_n) = (\<sigma> + \<rho>) mod (2 ^ oe_n)"
              unfolding cong_def .
            then have "\<tau> = (\<sigma> + \<rho>) mod (2 ^ oe_n)"
              using mod_less \<open>\<tau> < 2 ^ oe_n\<close> by simp
            define i where "i = (\<sigma> + \<rho>) div (2 ^ oe_n)"
            have "\<tau> + i * 2 ^ oe_n = \<sigma> + \<rho>"
              unfolding \<open>\<tau> = (\<sigma> + \<rho>) mod (2 ^ oe_n)\<close> i_def
              by (simp add: mod_div_mult_eq)
            moreover have "i \<le> 1"
            proof (rule ccontr)
              assume "\<not> i \<le> 1"
              then have "i \<ge> 2" by simp
              then have "\<sigma> + \<rho> \<ge> 2 ^ (oe_n + 1)"
                using \<open>\<tau> + i * 2 ^ oe_n = \<sigma> + \<rho>\<close>
                by (metis div_exp_eq div_greater_zero_iff i_def pos2 power_one_right)
              then show False using a by simp
            qed
            hence "i = 0 \<or> i = 1" by linarith
            ultimately show ?thesis by auto
          qed
          moreover have "\<tau> = \<sigma> + \<rho> \<or> \<tau> + 2 ^ oe_n = \<sigma> + \<rho> \<Longrightarrow> [\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n)"
            by (metis cong_add_lcancel_0_nat cong_refl cong_sym cong_to_1'_nat mult_1)
          ultimately show "[\<tau> = \<sigma> + \<rho>] (mod 2 ^ oe_n) = (\<tau> = \<sigma> + \<rho> \<or> \<tau> + 2 ^ oe_n = \<sigma> + \<rho>)" by argo
        qed
      also have "... = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          (of_bool (\<tau> = \<sigma> + \<rho>) + of_bool (\<tau> + 2 ^ oe_n = \<sigma> + \<rho>)) *
         (int (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_Zn ! \<rho>))))"
        apply (intro_cong "[cong_tag_2 (*)]" more: semiring_1_sum_list_eq refl of_bool_disj_excl)
        by simp
      also have "... = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          of_bool (\<tau> = \<sigma> + \<rho>) * (int (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_Zn ! \<rho>)))) +
          (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          of_bool (\<tau> + 2 ^ oe_n = \<sigma> + \<rho>) * (int (Nat_LSBF.to_nat (A.num_Zn ! \<sigma>)) * int (Nat_LSBF.to_nat (B.num_Zn ! \<rho>))))"
        by (simp add: int_distrib(1) sum_list_addf)
      also have "... = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          int (of_bool (\<tau> = \<sigma> + \<rho>) * ((Nat_LSBF.to_nat (A.num_Zn ! \<sigma>) * Nat_LSBF.to_nat (B.num_Zn ! \<rho>))))) +
          (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          int (of_bool (\<tau> + 2 ^ oe_n = \<sigma> + \<rho>) * ((Nat_LSBF.to_nat (A.num_Zn ! \<sigma>) * (Nat_LSBF.to_nat (B.num_Zn ! \<rho>))))))"
        apply (intro_cong "[cong_tag_2 (+)]" more: semiring_1_sum_list_eq)
        by simp_all
      also have "... = int (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          of_bool (\<tau> = \<sigma> + \<rho>) * ((Nat_LSBF.to_nat (A.num_Zn ! \<sigma>) * Nat_LSBF.to_nat (B.num_Zn ! \<rho>)))) +
          int (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. \<Sum>\<rho>\<leftarrow>[0..<2 ^ oe_n].
          of_bool (\<tau> + 2 ^ oe_n = \<sigma> + \<rho>) * ((Nat_LSBF.to_nat (A.num_Zn ! \<sigma>) * (Nat_LSBF.to_nat (B.num_Zn ! \<rho>)))))"
        by (simp add: sum_list_int)
      also have "... = int (\<gamma>' \<tau>) + int (\<gamma>' (\<tau> + 2 ^ oe_n))"
        unfolding \<gamma>'_def by argo
      finally show "[int (\<gamma>' \<tau>) + int (\<gamma>' (2 ^ oe_n + \<tau>)) = c' ! \<tau>] (mod 2 ^ (n + 2))"
        unfolding cong_def by (simp add: add.commute)
    qed
    have \<eta>_carrier: "length (\<eta> ! j) = n + 2" if "j < 2 ^ (oe_n - 1)" for j
    proof -
      have "\<eta> ! j = Znr.add_mod
        (Znr.subtract_mod (take (n + 2) (\<gamma> ! 0 ! j)) (take (n + 2) (\<gamma> ! 1 ! j)))
        (Znr.subtract_mod (take (n + 2) (\<gamma> ! 2 ! j)) (take (n + 2) (\<gamma> ! 3 ! j)))"
        unfolding \<eta>_def apply (intro nth_map4) using sc\<gamma> that by simp_all
      then show ?thesis using Znr.add_mod_closed by simp
    qed
    have \<eta>_residues: "Znr.to_residue_ring (\<eta> ! j) = z' j mod 2 ^ (n + 2)"
      if "j < 2 ^ (oe_n - 1)" for j
    proof -
      have "Znr.to_residue_ring (\<eta> ! j) =
        Znr.to_residue_ring (
        Znr.add_mod
        (Znr.subtract_mod (take (n + 2) (\<gamma> ! 0 ! j)) (take (n + 2) (\<gamma> ! 1 ! j)))
        (Znr.subtract_mod (take (n + 2) (\<gamma> ! 2 ! j)) (take (n + 2) (\<gamma> ! 3 ! j))))"
        unfolding \<eta>_def
        apply (intro arg_cong[where f = Znr.to_residue_ring] nth_map4)
        using \<open>j < 2 ^ (oe_n - 1)\<close> sc\<gamma>
        by simp_all
      also have "... =
        Znr.to_residue_ring (Znr.subtract_mod (take (n + 2) (\<gamma> ! 0 ! j)) (take (n + 2) (\<gamma> ! 1 ! j))) \<oplus>\<^bsub>Zn\<^esub>
        Znr.to_residue_ring (Znr.subtract_mod (take (n + 2) (\<gamma> ! 2 ! j)) (take (n + 2) (\<gamma> ! 3 ! j)))"
        by (intro Znr.add_mod_correct)
      also have "... =
          (Znr.to_residue_ring (take (n + 2) (\<gamma> ! 0 ! j)) \<ominus>\<^bsub>Zn\<^esub>
          Znr.to_residue_ring (take (n + 2) (\<gamma> ! 1 ! j))) \<oplus>\<^bsub>Zn\<^esub>
          (Znr.to_residue_ring (take (n + 2) (\<gamma> ! 2 ! j)) \<ominus>\<^bsub>Zn\<^esub>
          Znr.to_residue_ring (take (n + 2) (\<gamma> ! 3 ! j)))"
        apply (intro arg_cong2[where f = "(\<oplus>\<^bsub>Zn\<^esub>)"])
        subgoal
          using less_exp[of "n + 2"] by (intro Znr.subtract_mod_correct) simp_all
        subgoal
          using less_exp[of "n + 2"] by (intro Znr.subtract_mod_correct) simp_all
        done
      also have "... =
        (Znr.to_residue_ring (take (n + 2) (\<gamma> ! 0 ! j)) \<oplus>\<^bsub>Zn\<^esub>
        Znr.to_residue_ring (take (n + 2) (\<gamma> ! 2 ! j))) \<ominus>\<^bsub>Zn\<^esub>
        (Znr.to_residue_ring (take (n + 2) (\<gamma> ! 1 ! j)) \<oplus>\<^bsub>Zn\<^esub>
        Znr.to_residue_ring (take (n + 2) (\<gamma> ! 3 ! j)))"
        apply (intro Znr.diff_sum)
        using Znr.to_residue_ring_in_carrier by simp_all
      also have "... =
        (int (Nat_LSBF.to_nat (take (n + 2) (\<gamma> ! 0 ! j))) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (Nat_LSBF.to_nat (take (n + 2) (\<gamma> ! 2 ! j))) mod 2 ^ (n + 2)) \<ominus>\<^bsub>Zn\<^esub>
        (int (Nat_LSBF.to_nat (take (n + 2) (\<gamma> ! 1 ! j))) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (Nat_LSBF.to_nat (take (n + 2) (\<gamma> ! 3 ! j))) mod 2 ^ (n + 2))"
        unfolding Znr.to_residue_ring_def by simp
      also have "... =
        (int (Nat_LSBF.to_nat (\<gamma> ! 0 ! j)) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (Nat_LSBF.to_nat (\<gamma> ! 2 ! j)) mod 2 ^ (n + 2)) \<ominus>\<^bsub>Zn\<^esub>
        (int (Nat_LSBF.to_nat (\<gamma> ! 1 ! j)) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (Nat_LSBF.to_nat (\<gamma> ! 3 ! j)) mod 2 ^ (n + 2))"
        apply (intro_cong "[cong_tag_2 (\<lambda>i j. i \<ominus>\<^bsub>Zn\<^esub> j), cong_tag_2 (\<oplus>\<^bsub>Zn\<^esub>)]")
        by (simp_all add: to_nat_take zmod_int)
      also have "... =
        (int (\<gamma>' (0 * 2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (\<gamma>' (2 * 2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2)) \<ominus>\<^bsub>Zn\<^esub>
        (int (\<gamma>' (1 * 2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (\<gamma>' (3 * 2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2))"
        apply (intro_cong "[cong_tag_2 (\<lambda>i j. i \<ominus>\<^bsub>Zn\<^esub> j), cong_tag_2 (\<oplus>\<^bsub>Zn\<^esub>), cong_tag_2 (mod), cong_tag_1 int]" more: refl to_nat_\<gamma> \<open>j < 2 ^ (oe_n - 1)\<close>)
        by simp_all
      also have "... =
        (int (\<gamma>' j) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (\<gamma>' (2 ^ oe_n + j)) mod 2 ^ (n + 2)) \<ominus>\<^bsub>Zn\<^esub>
        (int (\<gamma>' (2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2) \<oplus>\<^bsub>Zn\<^esub>
        int (\<gamma>' (2 ^ oe_n + (2 ^ (oe_n - 1) + j))) mod 2 ^ (n + 2))"
        apply (intro_cong "[cong_tag_2 (\<lambda>i j. i \<ominus>\<^bsub>Zn\<^esub> j), cong_tag_2 (\<oplus>\<^bsub>Zn\<^esub>), cong_tag_2 (mod), cong_tag_1 int, cong_tag_1 \<gamma>']" more: refl)
        using two_pow_oe_n_as_halves by simp_all
      also have "... =
        (int (\<gamma>' j) mod 2 ^ (n + 2) +
        int (\<gamma>' (2 ^ oe_n + j)) mod 2 ^ (n + 2)) mod 2 ^ (n + 2) \<ominus>\<^bsub>Zn\<^esub>
        (int (\<gamma>' (2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2) +
        int (\<gamma>' (2 ^ oe_n + (2 ^ (oe_n - 1) + j))) mod 2 ^ (n + 2)) mod 2 ^ (n + 2)"
        apply (intro_cong "[cong_tag_2 (\<lambda>i j. i \<ominus>\<^bsub>Zn\<^esub> j)]")
        unfolding Znr.res_add_eq
        subgoal by (intro arg_cong[where f = "\<lambda>i. _ mod i"], unfold int_exp_hom[symmetric], simp)
        subgoal by (intro arg_cong[where f = "\<lambda>i. _ mod i"], simp)
        done
      also have "... =
        (int (\<gamma>' j) + int (\<gamma>' (2 ^ oe_n + j))) mod 2 ^ (n + 2) \<ominus>\<^bsub>Zn\<^esub>
        (int (\<gamma>' (2 ^ (oe_n - 1) + j)) +
        int (\<gamma>' (2 ^ oe_n + (2 ^ (oe_n - 1) + j)))) mod 2 ^ (n + 2)"
        by (intro_cong "[cong_tag_2 (\<lambda>i j. i \<ominus>\<^bsub>Zn\<^esub> j)]" more: mod_add_eq)
      also have "... = ((c' ! j) mod 2 ^ (n + 2)) \<ominus>\<^bsub>Zn\<^esub> ((c' ! (2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2))"
        apply (intro arg_cong2[where f = "\<lambda>i j. i \<ominus>\<^bsub>Zn\<^esub> j"])
        using \<gamma>c unfolding cong_def using \<open>j < 2 ^ (oe_n - 1)\<close> index_intros[of j]
        by simp_all
      also have "... = (c' ! j - c' ! (2 ^ (oe_n - 1) + j)) mod 2 ^ (n + 2)"
        unfolding Znr.residues_minus_eq
        by (simp add: mod_diff_eq)
      also have "... = (c' ! j - c' ! (2 ^ (oe_n - 1) + j) + 2 ^ (oe_n + 2 ^ n)) mod 2 ^ (n + 2)"
      proof -
        have "oe_n \<ge> n" unfolding oe_n_def by simp
        moreover have "2 ^ n \<ge> n + 2" using aux_ineq_3[OF n_gt_1] .
        ultimately have "oe_n + 2 ^ n \<ge> n + 2"
          by simp
        then have "(2::int) ^ (n + 2) dvd 2 ^ (oe_n + 2 ^ n)"
          apply (intro le_imp_power_dvd) .
        then have "(2::int) ^ (oe_n + 2 ^ n) mod 2 ^ (n + 2) = 0"
          using dvd_imp_mod_0 by blast
        then show ?thesis using mod_add_right_eq by fastforce
      qed
      also have "... = z' j mod 2 ^ (n + 2)"
        unfolding z'_def using \<open>j < 2 ^ (oe_n - 1)\<close> by presburger
      finally show "Znr.to_residue_ring (\<eta> ! j) = z' j mod 2 ^ (n + 2)" .
    qed


    (* goal 2: \<xi> contains the residues of z_j mod F_n *)
    define c'_mod where "c'_mod = map (\<lambda>i. i mod Fnr.n) c'"
    then have "length c'_mod = 2 ^ oe_n" using \<open>length c' = 2 ^ oe_n\<close> by simp
    have c'_mod_carrier: "\<And>j. j < 2 ^ oe_n \<Longrightarrow> c'_mod ! j \<in> carrier Fn"
      unfolding c'_mod_def
      using Fnr.mod_in_carrier \<open>length c' = 2 ^ oe_n\<close> by simp
    have c'_mod_eq: "c'_mod = Fnr.cyclic_convolution (2 ^ oe_n) (map Fnr.to_residue_ring A.num_blocks) (map Fnr.to_residue_ring B.num_blocks)"
    proof (intro nth_equalityI)
      show "length c'_mod = length
     (Fnr.cyclic_convolution (2 ^ oe_n) (map Fnr.to_residue_ring A.num_blocks)
       (map Fnr.to_residue_ring B.num_blocks))"
        by (simp add: \<open>length c'_mod = 2 ^ oe_n\<close>)
      fix i
      assume "i < length c'_mod"
      then have "i < 2 ^ oe_n" using \<open>length c'_mod = 2 ^ oe_n\<close> by simp
      then have "c'_mod ! i = (\<Sum>\<sigma>\<leftarrow>[0..<2 ^ oe_n]. int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) *
                  int (Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + i - \<sigma>) mod 2 ^ oe_n)))) mod int Fnr.n"
        unfolding c'_mod_def using c'_nth[OF \<open>i < 2 ^ oe_n\<close>] \<open>length c' = 2 ^ oe_n\<close> by simp
      also have "... = (\<Oplus>\<^bsub>Fn\<^esub>\<sigma>\<leftarrow>[0..< 2 ^ oe_n]. (int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) *
                  int (Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + i - \<sigma>) mod 2 ^ oe_n)))) mod int Fnr.n)"
        by (intro Fnr.monoid_sum_list_eq_sum_list'[symmetric])
      also have "... = (\<Oplus>\<^bsub>Fn\<^esub>\<sigma>\<leftarrow>[0..< 2 ^ oe_n]. ((int (Nat_LSBF.to_nat (A.num_blocks ! \<sigma>)) mod int Fnr.n) *
                  (int (Nat_LSBF.to_nat (B.num_blocks ! ((2 ^ oe_n + i - \<sigma>) mod 2 ^ oe_n))) mod int Fnr.n))
                  mod int Fnr.n)"
        by (intro Fnr.monoid_sum_list_cong mod_mult_eq[symmetric])
      also have "... = (\<Oplus>\<^bsub>Fn\<^esub>\<sigma>\<leftarrow>[0..< 2 ^ oe_n]. (Fnr.to_residue_ring (A.num_blocks ! \<sigma>) *
                  Fnr.to_residue_ring (B.num_blocks ! ((2 ^ oe_n + i - \<sigma>) mod 2 ^ oe_n))) mod int Fnr.n)"
        unfolding Fnr.to_residue_ring.simps by argo
      also have "... = (\<Oplus>\<^bsub>Fn\<^esub>\<sigma>\<leftarrow>[0..< 2 ^ oe_n]. Fnr.to_residue_ring (A.num_blocks ! \<sigma>) \<otimes>\<^bsub>Fn\<^esub>
                  Fnr.to_residue_ring (B.num_blocks ! ((2 ^ oe_n + i - \<sigma>) mod 2 ^ oe_n)))"
        unfolding Fnr.res_mult_eq by argo
      also have "... = (\<Oplus>\<^bsub>Fn\<^esub>\<sigma>\<leftarrow>[0..< 2 ^ oe_n]. map Fnr.to_residue_ring A.num_blocks ! \<sigma> \<otimes>\<^bsub>Fn\<^esub>
                  map Fnr.to_residue_ring B.num_blocks ! ((2 ^ oe_n + i - \<sigma>) mod 2 ^ oe_n))"
        apply (intro_cong "[cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: Fnr.monoid_sum_list_cong nth_map[symmetric])
        subgoal using A.length_num_blocks by simp
        subgoal using B.length_num_blocks by simp
        done
      also have "... = Fnr.cyclic_convolution (2 ^ oe_n) (map Fnr.to_residue_ring A.num_blocks)
                  (map Fnr.to_residue_ring B.num_blocks) ! i"
        by (intro Fnr.cyclic_convolution_nth[symmetric] \<open>i < 2 ^ oe_n\<close>)
      finally show "c'_mod ! i =
         Fnr.cyclic_convolution (2 ^ oe_n) (map Fnr.to_residue_ring A.num_blocks)
          (map Fnr.to_residue_ring B.num_blocks) ! i" .
    qed
    have fill_a': "map Fnr.to_residue_ring A.num_blocks = map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) A.num_blocks)"
      apply (intro nth_equalityI)
      subgoal by simp
      subgoal for i
        unfolding Fnr.to_residue_ring.simps by simp
      done
    have fill_b': "map Fnr.to_residue_ring B.num_blocks = map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) B.num_blocks)"
      apply (intro nth_equalityI)
      subgoal by simp
      subgoal for i
        unfolding Fnr.to_residue_ring.simps by simp
      done
    have aux0: "Fnr.NTT \<mu> c'_mod = map2 (\<otimes>\<^bsub>Fn\<^esub>) (Fnr.NTT \<mu> (map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) A.num_blocks)))
            (Fnr.NTT \<mu> (map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) B.num_blocks)))"
    proof (intro nth_equalityI)
      show "length (Fnr.NTT \<mu> c'_mod) = length (map2 (\<otimes>\<^bsub>Fn\<^esub>)
        (Fnr.NTT \<mu> (map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) A.num_blocks)))
        (Fnr.NTT \<mu> (map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) B.num_blocks))))"
        using \<open>length c'_mod = 2 ^ oe_n\<close> A.length_num_blocks B.length_num_blocks by simp
      fix i :: nat
      assume "i < length (Fnr.NTT \<mu> c'_mod)"
      then have "i < 2 ^ oe_n" using \<open>length c'_mod = 2 ^ oe_n\<close> by simp
      have "Fnr.NTT \<mu> c'_mod ! i =
          Fnr.NTT \<mu> (map Fnr.to_residue_ring A.num_blocks) ! i \<otimes>\<^bsub>Fn\<^esub>
          Fnr.NTT \<mu> (map Fnr.to_residue_ring B.num_blocks) ! i"
        unfolding c'_mod_eq
        apply (intro Fnr.convolution_rule[symmetric] set_subseteqI)
        subgoal using A.length_num_blocks by simp
        subgoal using B.length_num_blocks by simp
        subgoal using Fnr.to_residue_ring_in_carrier by simp
        subgoal using Fnr.to_residue_ring_in_carrier by simp
        subgoal using \<mu>_root_of_unity .
        subgoal using \<open>i < 2 ^ oe_n\<close> .
        done
      then show "Fnr.NTT \<mu> c'_mod ! i = map2 (\<otimes>\<^bsub>Fn\<^esub>)
          (Fnr.NTT \<mu> (map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) A.num_blocks)))
          (Fnr.NTT \<mu> (map Fnr.to_residue_ring (map (fill (2 ^ (n + 1))) B.num_blocks))) ! i"
        unfolding fill_a' fill_b'
        using A.length_num_blocks B.length_num_blocks \<open>length c'_mod = 2 ^ oe_n\<close>
        by (simp add: \<open>i < 2 ^ oe_n\<close>)
    qed
    have IH_inst: "Fnr.to_residue_ring (schoenhage_strassen n (evens_odds False A.num_dft ! i) (evens_odds False B.num_dft ! i)) =
      Fnr.to_residue_ring (evens_odds False A.num_dft ! i) \<otimes>\<^bsub>int_lsbf_fermat.Fn n\<^esub>
      Fnr.to_residue_ring (evens_odds False B.num_dft ! i) \<and>
      schoenhage_strassen n (evens_odds False A.num_dft ! i) (evens_odds False B.num_dft ! i) \<in> Fnr.fermat_non_unique_carrier"
      if "i < 2 ^ (oe_n - 1)" for i
      apply (intro "less.IH" n_lt_m)
      subgoal
        apply (rule set_mp[OF A.num_dft_carrier])
        apply (rule set_mp[OF set_evens_odds])
        apply (rule nth_mem)
        apply (unfold A.num_dft_odds_def[symmetric] A.length_num_dft_odds)
        apply (rule that)
        done
      subgoal
        apply (rule set_mp[OF B.num_dft_carrier])
        apply (rule set_mp[OF set_evens_odds])
        apply (rule nth_mem)
        apply (unfold B.num_dft_odds_def[symmetric] B.length_num_dft_odds)
        apply (rule that)
        done
      done
    have aux4: "Fnr.to_residue_ring (c_dft_odds ! i) =
          Fnr.to_residue_ring (A.num_dft_odds ! i) \<otimes>\<^bsub>Fn\<^esub>
          Fnr.to_residue_ring (B.num_dft_odds ! i)"
          "c_dft_odds ! i \<in> Fnr.fermat_non_unique_carrier"
      if "i < 2 ^ (oe_n - 1)" for i
    proof -
      from that have "i < length c_dft_odds" using length_c_dft_odds by simp
      then have "c_dft_odds ! i = schoenhage_strassen n (A.num_dft_odds ! i) (B.num_dft_odds ! i)"
        unfolding c_dft_odds_def by simp
      also have "Fnr.to_residue_ring ... =
        Fnr.to_residue_ring (A.num_dft_odds ! i) \<otimes>\<^bsub>int_lsbf_fermat.Fn n\<^esub>
        Fnr.to_residue_ring (B.num_dft_odds ! i) \<and>
        ... \<in> Fnr.fermat_non_unique_carrier"
        using IH_inst[OF that]
        using A.num_dft_odds_def B.num_dft_odds_def Fn_def
        by argo
      finally show "Fnr.to_residue_ring (c_dft_odds ! i) =
          Fnr.to_residue_ring (A.num_dft_odds ! i) \<otimes>\<^bsub>Fn\<^esub>
          Fnr.to_residue_ring (B.num_dft_odds ! i)"
          "c_dft_odds ! i \<in> Fnr.fermat_non_unique_carrier "
        by simp_all
    qed
    then have to_res_c_dft_odds: "map Fnr.to_residue_ring c_dft_odds = map2 (\<otimes>\<^bsub>Fn\<^esub>)
      (map Fnr.to_residue_ring A.num_dft_odds)
      (map Fnr.to_residue_ring B.num_dft_odds)"
      apply (intro nth_equalityI)
      using length_c_dft_odds A.length_num_dft_odds B.length_num_dft_odds
      by auto
    have "set c'_mod \<subseteq> carrier Fn"
      apply (intro set_subseteqI)
      using c'_mod_carrier \<open>length c'_mod = 2 ^ oe_n\<close> by simp
    have "Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) =
      map ((\<otimes>\<^bsub>Fn\<^esub>) (Fnr.nat_embedding (2 ^ oe_n))) c'_mod"
      apply (intro Fnr.inversion_rule)
      subgoal by simp
      subgoal using \<mu>_prim_root .
      subgoal premises prems for i
        apply (intro Fnr.sufficiently_good[of _ _ oe_n])
        subgoal using \<mu>_prim_root .
        subgoal using \<mu>_halfway_property by blast
        subgoal by (fact prems)
        done
      subgoal using \<open>length c'_mod = 2 ^ oe_n\<close> by simp
      subgoal using \<open>set c'_mod \<subseteq> carrier Fn\<close> .
      done
    also have "... = map ((\<otimes>\<^bsub>Fn\<^esub>) (2 ^ oe_n mod int Fnr.n)) c'_mod"
      unfolding Fnr.nat_embedding_eq by simp
    (* This step will be reversed later, but the simpler expressions are worth it *)
    also have "... = map ((\<otimes>\<^bsub>Fn\<^esub>) (2 ^ oe_n)) c'_mod"
      unfolding Fnr.pow_nat_eq[symmetric] two_oe_n by argo
    finally have aux1: "Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! j =
       (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (c'_mod ! j)" if "j < 2 ^ oe_n" for j
      using \<open>length c'_mod = 2 ^ oe_n\<close> that by simp
    have c'_NTT_NTT_carrier: "Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! j \<in> carrier Fn" if "j < 2 ^ oe_n" for j
      apply (intro set_subseteqD[OF Fnr.NTT_closed] Fnr.NTT_closed Fnr.Units_inv_closed \<mu>_Units_Fn \<mu>_carrier_Fn \<open>set c'_mod \<subseteq> carrier Fn\<close>)
      by (simp add: \<open>length c'_mod = 2 ^ oe_n\<close> that)
    have aux2: "inv\<^bsub>Fn\<^esub> (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! j =
       (c'_mod ! j)" if "j < 2 ^ oe_n" for j
      apply (intro Fnr.inv_cancel_left)
      subgoal using c'_NTT_NTT_carrier that by presburger
      subgoal using c'_mod_carrier[OF that] by simp
      subgoal unfolding two_oe_n[symmetric] by (intro Fnr.Units_pow_closed Fnr.two_is_unit)
      subgoal using aux1[OF that] .
      done
    have aux3: "c'_mod ! j \<ominus>\<^bsub>Fn\<^esub> c'_mod ! (2 ^ (oe_n - 1) + j) =
        (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (oe_n + prim_root_exponent * j - 1) \<otimes>\<^bsub>Fn\<^esub>
         Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (map Fnr.to_residue_ring c_dft_odds) ! j"
      if "j < 2 ^ (oe_n - 1)" for j
    proof -
      have odd_indices: "\<And>i. i < 2 ^ (oe_n - 1) \<Longrightarrow> (2::nat) * i + 1 < 2 ^ oe_n"
      proof -
        fix i :: nat
        assume "i < 2 ^ (oe_n - 1)"
        then have "i + 1 \<le> 2 ^ (oe_n - 1)" by simp
        then have "2 * i + 2 \<le> 2 * 2 ^ (oe_n - 1)" by simp
        also have "... = 2 ^ oe_n" using two_pow_oe_n_as_halves by simp
        finally show "2 * i + 1 < 2 ^ oe_n" by simp
      qed
      have "c'_mod ! j \<ominus>\<^bsub>Fn\<^esub> c'_mod ! (2 ^ (oe_n - 1) + j) =
        inv\<^bsub>Fn\<^esub> (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! j) \<ominus>\<^bsub>Fn\<^esub>
        inv\<^bsub>Fn\<^esub> (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! (2 ^ (oe_n - 1) + j))"
        apply (intro arg_cong2[where f = "\<lambda>i j. i \<ominus>\<^bsub>Fn\<^esub> j"])
        using aux2 index_intros[OF that] by simp_all
      also have "... = inv\<^bsub>Fn\<^esub> (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! j \<ominus>\<^bsub>Fn\<^esub>
                        Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu>) (Fnr.NTT \<mu> c'_mod) ! (2 ^ (oe_n - 1) + j))"
        apply (intro Fnr.r_distr_diff[symmetric])
        subgoal by (intro Fnr.Units_closed Fnr.Units_inv_Units two_oe_n_Units_Fn)
        subgoal using index_intros[OF that] c'_NTT_NTT_carrier by presburger
        subgoal using index_intros[OF that] c'_NTT_NTT_carrier by presburger
        done
      also have "... = inv\<^bsub>Fn\<^esub> (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (Fnr.nat_embedding 2 \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> j \<otimes>\<^bsub>Fn\<^esub>
         Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat))
          (map ((!) (Fnr.NTT \<mu> c'_mod)) (filter odd [0..<2 ^ oe_n])) ! j))"
        unfolding two_pow_oe_n_div_2[symmetric]
        apply (intro arg_cong2[where f = "(\<otimes>\<^bsub>Fn\<^esub>)"] refl Fnr.NTT_diffs)
        subgoal using oe_n_gt_0 by simp
        subgoal by (intro Fnr.primitive_root_inv \<mu>_prim_root) simp
        subgoal by (simp add: \<open>length c'_mod = 2 ^ oe_n\<close>)
        subgoal using \<open>j < 2 ^ (oe_n - 1)\<close> unfolding \<open>2 ^ (oe_n - 1) = 2 ^ oe_n div 2\<close> .
        subgoal by (intro Fnr.NTT_closed \<open>set c'_mod \<subseteq> carrier Fn\<close> \<mu>_carrier_Fn)
        subgoal by (intro Fnr.inv_halfway_property \<mu>_Units_Fn \<mu>_halfway_property)
        done
      also have "... = inv\<^bsub>Fn\<^esub> (2 ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (2 \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> j \<otimes>\<^bsub>Fn\<^esub>
         Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat))
          (map ((!) (Fnr.NTT \<mu> c'_mod)) (filter odd [0..<2 ^ oe_n])) ! j))"
        using Fnr.nat_embedding_eq Fnr.carrier_mod_eq[OF Fnr.two_in_carrier] by simp
      also have "Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (map ((!) (Fnr.NTT \<mu> c'_mod)) (filter odd [0..<2 ^ oe_n])) ! j =
        Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (
          map ((!) (map2 (\<otimes>\<^bsub>Fn\<^esub>)
            (Fnr.NTT \<mu> (map Fnr.to_residue_ring A.num_blocks_carrier))
            (Fnr.NTT \<mu> (map Fnr.to_residue_ring B.num_blocks_carrier))
          ))
          (filter odd [0..<2 ^ oe_n])
        ) ! j"
        using aux0 unfolding A.num_blocks_carrier_def B.num_blocks_carrier_def by argo
      also have "... = Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (
          map ((!) (map2 (\<otimes>\<^bsub>Fn\<^esub>)
            (map Fnr.to_residue_ring A.num_dft)
            (map Fnr.to_residue_ring B.num_dft)
          ))
          (filter odd [0..<2 ^ oe_n])
        ) ! j"
        by (intro_cong "[cong_tag_2 (!), cong_tag_2 Fnr.NTT, cong_tag_2 map, cong_tag_1 (!), cong_tag_2 zip]" more: refl A.to_res_num_dft[symmetric] B.to_res_num_dft[symmetric])
      also have "map ((!) (map2 (\<otimes>\<^bsub>Fn\<^esub>)
            (map Fnr.to_residue_ring A.num_dft)
            (map Fnr.to_residue_ring B.num_dft)
          ))
          (filter odd [0..<2 ^ oe_n]) =
          map2 (\<otimes>\<^bsub>Fn\<^esub>) (map Fnr.to_residue_ring (map ((!) A.num_dft) (filter odd [0..<length A.num_dft])))
           (map Fnr.to_residue_ring (map ((!) B.num_dft) (filter odd [0..<length B.num_dft])))"
        apply (intro nth_equalityI)
        subgoal by (simp add: length_filter_odd)
        subgoal for i
          using odd_indices[of i] length_filter_odd[of "2 ^ oe_n"] filter_odd_nth[of i "2 ^ oe_n"] A.length_num_dft B.length_num_dft two_pow_oe_n_as_halves
          by simp
        done
      also have "... =
          map2 (\<otimes>\<^bsub>Fn\<^esub>) (map Fnr.to_residue_ring (evens_odds False A.num_dft))
           (map Fnr.to_residue_ring (evens_odds False B.num_dft))"
        using filter_comprehension_evens_odds by metis
      also have "... = map Fnr.to_residue_ring c_dft_odds"
        using to_res_c_dft_odds[symmetric] unfolding A.num_dft_odds_def B.num_dft_odds_def .
      also have "inv\<^bsub>Fn\<^esub> ((2::int) ^ oe_n) \<otimes>\<^bsub>Fn\<^esub> (2 \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> j \<otimes>\<^bsub>Fn\<^esub>
           Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (map Fnr.to_residue_ring c_dft_odds) ! j)) =
            (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> oe_n \<otimes>\<^bsub>Fn\<^esub> ((inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (-1::int) \<otimes>\<^bsub>Fn\<^esub> ((inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (prim_root_exponent * j) \<otimes>\<^bsub>Fn\<^esub>
           Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (map Fnr.to_residue_ring c_dft_odds) ! j))"
        apply (intro_cong "[cong_tag_2 (\<otimes>\<^bsub>Fn\<^esub>)]" more: refl)
        subgoal
          unfolding two_oe_n[symmetric] by (intro Fnr.inv_nat_pow Fnr.two_is_unit)
        subgoal by (metis Fnr.Units_inv_Units Fnr.Units_inv_inv Fnr.units_inv_int_pow Fnr.two_is_unit)
        subgoal
        proof -
          have "inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> j = inv\<^bsub>Fn\<^esub> (\<mu> [^]\<^bsub>Fn\<^esub> j)"
            using Fnr.inv_nat_pow[OF \<mu>_Units_Fn, symmetric] .
          also have "... = inv\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> (prim_root_exponent * j))"
            unfolding \<mu>_def Fnr.nat_pow_pow[OF Fnr.two_in_carrier] by argo
          also have "... = inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (prim_root_exponent * j)"
            using Fnr.inv_nat_pow[OF Fnr.two_is_unit] .
          finally show ?thesis .
        qed
        done
      also have "... = inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> oe_n \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (-1::int) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (prim_root_exponent * j) \<otimes>\<^bsub>Fn\<^esub>
           Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (map Fnr.to_residue_ring c_dft_odds) ! j"
        apply (intro Fnr.assoc4)
        subgoal by (intro Fnr.nat_pow_closed Fnr.Units_inv_closed Fnr.two_is_unit)
        subgoal by (intro Fnr.Units_closed Fnr.int_pow_closed Fnr.Units_inv_Units Fnr.two_is_unit)
        subgoal by (intro Fnr.nat_pow_closed Fnr.Units_inv_closed Fnr.two_is_unit)
        subgoal
          apply (intro set_subseteqD[OF Fnr.NTT_closed])
          subgoal
            apply (intro set_subseteqI)
            using Fnr.to_residue_ring_in_carrier
            by simp
          subgoal by (intro Fnr.Units_closed Fnr.Units_pow_closed Fnr.Units_inv_Units \<mu>_Units_Fn)
          subgoal using \<open>j < 2 ^ (oe_n - 1)\<close> by (simp add: length_c_dft_odds)
          done
        done
      also have "inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> oe_n \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (-1::int) \<otimes>\<^bsub>Fn\<^esub> inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (prim_root_exponent * j) =
        inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (oe_n + prim_root_exponent * j - 1)"
        unfolding int_pow_int[symmetric] Fnr.int_pow_mult[OF Fnr.Units_inv_Units[OF Fnr.two_is_unit]]
        apply (intro arg_cong[where f = "([^]\<^bsub>Fn\<^esub>) _"])
        using oe_n_gt_0 by linarith
      finally show "c'_mod ! j \<ominus>\<^bsub>Fn\<^esub> c'_mod ! (2 ^ (oe_n - 1) + j) =
        inv\<^bsub>Fn\<^esub> 2 [^]\<^bsub>Fn\<^esub> (oe_n + prim_root_exponent * j - 1) \<otimes>\<^bsub>Fn\<^esub>
         Fnr.NTT (inv\<^bsub>Fn\<^esub> \<mu> [^]\<^bsub>Fn\<^esub> (2::nat)) (map Fnr.to_residue_ring c_dft_odds) ! j" .
    qed
    have c_dft_odds_carrier: "set c_dft_odds \<subseteq> Fnr.fermat_non_unique_carrier"
      unfolding c_dft_odds_def
      apply (intro set_subseteqI)
      using conjunct2[OF IH_inst] A.length_num_dft_odds B.length_num_dft_odds
      unfolding A.num_dft_odds_def B.num_dft_odds_def
      by simp
    have c_diffs_carrier: "c_diffs ! i \<in> Fnr.fermat_non_unique_carrier" if "i < 2 ^ (oe_n - 1)" for i
      unfolding c_diffs_def Fnr.ifft.simps
      apply (intro set_subseteqD[OF Fnr.fft_ifft_carrier[of _ "oe_n - 1"]])
      subgoal using length_c_dft_odds .
      subgoal using c_dft_odds_carrier .
      subgoal using Fnr.length_ifft[OF length_c_dft_odds] that by simp
      done
    have \<xi>'_residues: "Fnr.to_residue_ring (\<xi>' ! j) = z' j mod Fnr.n" if "j < 2 ^ (oe_n - 1)" for j
    proof -
      from that have "Fnr.to_residue_ring (\<xi>' ! j) = Fnr.to_residue_ring
     (Fnr.add_fermat
                (Fnr.divide_by_power_of_2 (c_diffs ! j) (oe_n + prim_root_exponent * j - 1))
                (Fnr.from_nat_lsbf (replicate (oe_n + 2 ^ n) False @ [True])))"
        unfolding \<xi>'_def by (simp add: length_c_diffs)
      also have "... = Fnr.to_residue_ring (Fnr.divide_by_power_of_2 (c_diffs ! j) (oe_n + prim_root_exponent * j - 1)) \<oplus>\<^bsub>Fn\<^esub>
          Fnr.to_residue_ring (Fnr.from_nat_lsbf (replicate (oe_n + 2 ^ n) False @ [True]))"
        apply (intro Fnr.add_fermat_correct)
        subgoal by (intro Fnr.divide_by_power_of_2_closed c_diffs_carrier that)
        subgoal by (intro Fnr.from_nat_lsbf_correct(1))
        done
      also have "... = Fnr.to_residue_ring (c_diffs ! j) \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (oe_n + prim_root_exponent * j - 1) \<oplus>\<^bsub>Fn\<^esub>
          Fnr.to_residue_ring (replicate (oe_n + 2 ^ n) False @ [True])"
        apply (intro arg_cong2[where f = "(\<oplus>\<^bsub>Fn\<^esub>)"])
        subgoal by (intro Fnr.divide_by_power_of_2_correct c_diffs_carrier that)
        subgoal by (intro Fnr.from_nat_lsbf_correct(2))
        done
      also have "Fnr.to_residue_ring (replicate (oe_n + 2 ^ n) False @ [True]) =
        (2 ^ (oe_n + 2 ^ n)) mod Fnr.n"
        by (simp add: zmod_int)
      also have "... = 2 [^]\<^bsub>Fn\<^esub> (oe_n + 2 ^ n)"
        using Fnr.pow_nat_eq[symmetric] by (simp add: zmod_int)
      also have "Fnr.to_residue_ring (c_diffs ! j) = 
        map Fnr.to_residue_ring
          (Fnr.ifft (prim_root_exponent * 2) c_dft_odds) ! j"
        unfolding c_diffs_def using length_c_dft_odds \<open>j < 2 ^ (oe_n - 1)\<close>
        apply (intro nth_map[symmetric])
        by (simp add: Fnr.length_fft_ifft)
      also have "... = Fnr.NTT ((inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (prim_root_exponent * 2)) (map Fnr.to_residue_ring c_dft_odds) ! j"
        apply (intro arg_cong2[where f = "(!)"] refl Fnr.ifft_correct[of _ "oe_n - 1" _ prim_root_exponent])
        subgoal using length_c_dft_odds .
        subgoal unfolding prim_root_exponent_def by simp
        subgoal unfolding prim_root_exponent_def oe_n_def using n_gt_1 by simp
        subgoal using oe_n_gt_1 by simp
        subgoal apply (intro set_subseteqI) using aux4 \<open>length c_dft_odds = 2 ^ (oe_n - 1)\<close> by fastforce
        done
      also have "... = Fnr.NTT 
        (inv\<^bsub>Fn\<^esub> (2 [^]\<^bsub>Fn\<^esub> (prim_root_exponent * 2)))
        (map Fnr.to_residue_ring c_dft_odds) ! j"
        by (intro arg_cong[where f = "\<lambda>a. Fnr.NTT a _ ! _"] Fnr.inv_nat_pow[symmetric] Fnr.two_is_unit)
      also have "... = Fnr.NTT (inv\<^bsub>Fn\<^esub> (\<mu> [^]\<^bsub>Fn\<^esub> (2::nat)))
         (map Fnr.to_residue_ring c_dft_odds) ! j"
        apply (intro_cong "[cong_tag_2 (!), cong_tag_2 Fnr.NTT, cong_tag_1 (\<lambda>j. inv\<^bsub>Fn\<^esub> j)]" more: refl)
        unfolding \<mu>_def
        by (intro Fnr.nat_pow_pow[symmetric] Fnr.two_in_carrier)
      also have "... \<otimes>\<^bsub>Fn\<^esub> (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (oe_n + prim_root_exponent * j - 1) =
        (inv\<^bsub>Fn\<^esub> 2) [^]\<^bsub>Fn\<^esub> (oe_n + prim_root_exponent * j - 1) \<otimes>\<^bsub>Fn\<^esub> ..."
        apply (intro Fnr.m_comm)
        subgoal
          apply (intro set_subseteqD[OF Fnr.NTT_closed])
          subgoal apply (intro set_subseteqI) using Fnr.to_residue_ring_in_carrier by simp
          subgoal by (intro Fnr.Units_closed Fnr.Units_inv_Units Fnr.Units_pow_closed \<mu>_Units_Fn)
          subgoal using \<open>j < 2 ^ (oe_n - 1)\<close> by (simp add: length_c_dft_odds)
          done
        subgoal
          by (intro Fnr.nat_pow_closed Fnr.Units_inv_closed Fnr.two_is_unit)
        done
      finally have "Fnr.to_residue_ring (\<xi>' ! j) =
        (c'_mod ! j \<ominus>\<^bsub>Fn\<^esub> c'_mod ! (2 ^ (oe_n - 1) + j)) \<oplus>\<^bsub>Fn\<^esub>
        2 [^]\<^bsub>Fn\<^esub> (oe_n + 2 ^ n)"
        unfolding aux3[OF \<open>j < 2 ^ (oe_n - 1)\<close>]
        using Fnr.inv_nat_pow[OF \<mu>_Units_Fn] by presburger
      also have "... = ((c'_mod ! j \<ominus>\<^bsub>Fn\<^esub> c'_mod ! (2 ^ (oe_n - 1) + j)) +
        2 [^]\<^bsub>Fn\<^esub> (oe_n + 2 ^ n)) mod Fnr.n"
        by (intro Fnr.res_add_eq)
      also have "... = ((c'_mod ! j - (c'_mod ! (2 ^ (oe_n - 1) + j))) mod Fnr.n +
        2 [^]\<^bsub>Fn\<^esub> (oe_n + 2 ^ n)) mod Fnr.n"
        by (intro_cong "[cong_tag_2 (mod), cong_tag_2 (+)]" more: refl Fnr.residues_minus_eq)
      also have "... = (((c' ! j) mod Fnr.n - (c' ! (2 ^ (oe_n - 1) + j)) mod Fnr.n) mod Fnr.n +
        2 [^]\<^bsub>Fn\<^esub> (oe_n + 2 ^ n)) mod Fnr.n"
        apply (intro_cong "[cong_tag_2 (mod), cong_tag_2 (+), cong_tag_2 (-)]" more: refl)
        unfolding c'_mod_def using \<open>j < 2 ^ (oe_n - 1)\<close> index_intros[of j] \<open>length c' = 2 ^ oe_n\<close>
        by simp_all
      also have "... = (c' ! j - c' ! (2 ^ (oe_n - 1) + j) +
        2 [^]\<^bsub>Fn\<^esub> (oe_n + 2 ^ n)) mod Fnr.n"
        by (simp only: mod_diff_eq mod_add_left_eq)
      also have "... = (c' ! j - c' ! (2 ^ (oe_n - 1) + j) +
        2 ^ (oe_n + 2 ^ n)) mod Fnr.n"
        by (simp only: Fnr.pow_nat_eq mod_add_right_eq)
      also have "... = z' j mod Fnr.n"
        unfolding z'_def using \<open>j < 2 ^ (oe_n - 1)\<close> by presburger
      finally show "Fnr.to_residue_ring (\<xi>' ! j) = z' j mod Fnr.n" .
    qed

    (* solve the chinese remainder problem to obtain z *)
    have \<xi>'_carrier: "\<xi>' ! i \<in> Fnr.fermat_non_unique_carrier" if "i < 2 ^ (oe_n - 1)" for i
    proof -
      from that have "\<xi>' ! i = Fnr.add_fermat
              (Fnr.divide_by_power_of_2 (c_diffs ! i)
                (oe_n + prim_root_exponent * ([0..<2 ^ (oe_n - 1)] ! i) - 1))
              (Fnr.from_nat_lsbf (replicate (oe_n + 2 ^ n) False @ [True]))" unfolding \<xi>'_def
        apply (intro nth_map2)
        using length_c_diffs by simp_all
      also have "... \<in> Fnr.fermat_non_unique_carrier"
        apply (intro Fnr.add_fermat_closed)
        subgoal
          by (intro Fnr.divide_by_power_of_2_closed that c_diffs_carrier)
        subgoal by (intro Fnr.from_nat_lsbf_correct(1))
        done
      finally show "\<xi>' ! i \<in> Fnr.fermat_non_unique_carrier" .
    qed
    have \<xi>_\<xi>': "Nat_LSBF.to_nat (\<xi> ! i) = Nat_LSBF.to_nat (\<xi>' ! i) mod Fnr.n"
      if "i < 2 ^ (oe_n - 1)" for i
      unfolding \<xi>_def using Fnr.reduce_correct[OF \<xi>'_carrier[OF that]]
      using that length_\<xi>' by simp
    have z'_bounds: "z' j \<ge> 0" "z' j < 2 ^ (oe_n + 1) * 2 ^ 2 ^ n" if "j < 2 ^ (oe_n - 1)" for j
    proof -
      have "z' j = c' ! j - c' ! (2 ^ (oe_n - 1) + j) + 2 ^ (oe_n + 2 ^ n)" (is "_ = ?z")
        unfolding z'_def using that by simp
      have "c' ! j \<ge> 0" "c' ! j < 2 ^ (oe_n + 2 ^ n)"
        using c'_upper_bound[of j] c'_lower_bound[of j] index_intros[of j] \<open>j < 2 ^ (oe_n - 1)\<close>
        by simp_all
      moreover have "c' ! (2 ^ (oe_n - 1) + j) \<ge> 0" "c' ! (2 ^ (oe_n - 1) + j) < 2 ^ (oe_n + 2 ^ n)"
        using c'_upper_bound c'_lower_bound index_intros[of j] \<open>j < 2 ^ (oe_n - 1)\<close> by simp_all
      ultimately have "?z \<ge> 0" "?z < 2 ^ (oe_n + 2 ^ n) + 2 ^ (oe_n + 2 ^ n)"
        by linarith+
      then have "?z < 2 ^ (oe_n + 1 + 2 ^ n)"
        by simp
      also have "... = 2 ^ (oe_n + 1) * 2 ^ 2 ^ n" by (simp add: power_add)
      finally show "z' j \<ge> 0" "z' j < 2 ^ (oe_n + 1) * 2 ^ 2 ^ n" using \<open>z' j = ?z\<close> \<open>?z \<ge> 0\<close> by simp_all
    qed
    have z_z': "Fmr.to_residue_ring (z ! j) = z' j" if "j < 2 ^ (oe_n - 1)" for j
    proof -
      from that have "z ! j = solve_special_residue_problem n (\<xi> ! j) (\<eta> ! j)"
        unfolding z_def using length_\<xi> length_\<eta> by simp
      then have "solves_special_residue_problem (Nat_LSBF.to_nat (z ! j)) n (Nat_LSBF.to_nat (\<xi> ! j)) (Nat_LSBF.to_nat (\<eta> ! j))"
        apply (intro solve_special_residue_problem_correct)
        subgoal using n_gt_1 by simp
        subgoal using \<eta>_carrier[OF that] by simp
        subgoal using \<xi>_\<xi>'[OF that] by simp
        subgoal .
        done
      moreover have "solves_special_residue_problem (nat (z' j)) n (Nat_LSBF.to_nat (\<xi> ! j)) (Nat_LSBF.to_nat (\<eta> ! j))"
        unfolding solves_special_residue_problem_def
        apply (intro conjI)
        subgoal
          apply (intro iffD2[OF nat_int_comparison(2)])
          unfolding nat_0_le[of "z' j", OF z'_bounds(1)[OF that]]
          unfolding int_ops
          apply (intro order.strict_trans2[OF z'_bounds(2)[OF that]])
          apply (intro mult_mono)
          unfolding oe_n_def by simp_all
        subgoal unfolding \<xi>_\<xi>'[OF that] using \<xi>'_residues[OF that, symmetric]
          apply (intro iffD1[OF int_int_eq])
          using nat_0_le[OF z'_bounds(1)[OF that], symmetric] zmod_int
          by simp
        subgoal
        proof -
          have "z' j mod 2 ^ (n + 2) = int (Nat_LSBF.to_nat (\<eta> ! j)) mod 2 ^ (n + 2)"
            using \<eta>_residues[OF that] unfolding Znr.to_residue_ring_def by simp
          also have "... = int (Nat_LSBF.to_nat (\<eta> ! j) mod 2 ^ (n + 2))"
            by (simp add: zmod_int)
          also have "... = int (Nat_LSBF.to_nat (\<eta> ! j))"
            apply (intro arg_cong[where f = int])
            using to_nat_length_bound \<eta>_carrier[OF that] mod_less by metis
          finally show ?thesis
            apply (intro iffD1[OF int_int_eq])
            using nat_0_le[OF z'_bounds(1)[OF that]] zmod_int by simp
        qed
        done
      ultimately have "nat (z' j) = Nat_LSBF.to_nat (z ! j)"
        using special_residue_problem_unique_solution by simp
      then have "int (Nat_LSBF.to_nat (z ! j)) = z' j" using nat_0_le[OF z'_bounds(1)[OF that]] by argo
      have "z' j \<in> carrier Fm"
        using z'_carrier z'_z'' index_intros that by simp
      then have "z' j mod Fmr.n = z' j"
        apply (intro Fmr.carrier_mod_eq) .
      with \<open>int (Nat_LSBF.to_nat (z ! j)) = z' j\<close> show "Fmr.to_residue_ring (z ! j) = z' j"
        by simp
    qed

    (* sum everything up *)
    have result_value: "Fmr.to_residue_ring result = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (z' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
    proof -
      have "Fmr.to_residue_ring result = Fmr.to_residue_ring z_sum"
        unfolding result_def by (rule Fmr.from_nat_lsbf_correct(2))
      also have "... = int (Nat_LSBF.to_nat z_sum) mod int Fmr.n"
        unfolding Fmr.to_residue_ring.simps by simp
      also have "Nat_LSBF.to_nat z_sum = (\<Sum>i\<leftarrow>[0..<length (z_filled @ z_consts)]. Nat_LSBF.to_nat ((z_filled @ z_consts) ! i) * 2 ^ (i * 2 ^ (n - 1)))"
        unfolding z_sum_def
        apply (intro combine_z_correct)
        subgoal by simp
        subgoal premises prems for zi
          unfolding set_append
        proof (cases "zi \<in> set z_filled")
          case True
          then obtain i where "zi = fill (2 ^ (n - 1)) i" "i \<in> set z"
            unfolding z_filled_def set_map by auto
          then show ?thesis using length_fill' by simp 
        next
          case False
          then have "zi = replicate (oe_n + 2 ^ n) False @ [True]"
            using prems unfolding z_consts_def by simp
          then have "length zi \<ge> 2 ^ n" by simp
          moreover have "2 ^ n \<ge> (2::nat) ^ (n - 1)" by simp
          ultimately show ?thesis by linarith
        qed
        done
      finally have "Fmr.to_residue_ring result = (\<Oplus>\<^bsub>Fm\<^esub>i\<leftarrow>[0..<length (z_filled @ z_consts)]. int (Nat_LSBF.to_nat ((z_filled @ z_consts) ! i) * 2 ^ (i * 2 ^ (n - 1))) mod Fmr.n)"
        unfolding Fmr.monoid_sum_list_eq_sum_list' sum_list_int .
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. int (Nat_LSBF.to_nat ((z_filled @ z_consts) ! i) * 2 ^ (i * 2 ^ (n - 1))) mod Fmr.n)"
        apply (intro arg_cong2[where f = Fmr.monoid_sum_list] refl arg_cong[where f = "\<lambda>i. [0..<i]"])
        by (simp add: length_z_filled length_z_consts two_pow_oe_n_as_halves)
      also have "... = (\<Oplus>\<^bsub>Fm\<^esub>i \<leftarrow> [0..<2 ^ oe_n]. (z' i) \<otimes>\<^bsub>Fm\<^esub> 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1)))"
        apply (intro Fmr.monoid_sum_list_cong)
        subgoal premises prems for i
        proof (cases "i < 2 ^ (oe_n - 1)")
          case True
          then have "int (Nat_LSBF.to_nat ((z_filled @ z_consts) ! i) * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n
            = int (Nat_LSBF.to_nat (z_filled ! i) * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n"
            using length_z_filled nth_append by metis
          also have "... = int (Nat_LSBF.to_nat (z ! i) * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n"
            unfolding z_filled_def using length_z True by simp
          also have "... = (int (Nat_LSBF.to_nat (z ! i)) mod int Fmr.n * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n"
            by (simp add: mod_mult_left_eq)
          also have "... = (z' i * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n"
            using z_z'[OF True] unfolding Fmr.to_residue_ring.simps by argo
          also have "... = (z' i * (2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n)) mod int Fmr.n"
            by (simp add: mod_mult_right_eq)
          also have "... = z' i \<otimes>\<^bsub>Fm\<^esub> (2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n)"
            by (rule Fmr.res_mult_eq[symmetric])
          also have "2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n = 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))"
            by (rule Fmr.pow_nat_eq[symmetric])
          finally show ?thesis .
        next
          case False
          define j where "j = i - 2 ^ (oe_n - 1)"
          then have "i = 2 ^ (oe_n - 1) + j" "j < 2 ^ (oe_n - 1)"
            subgoal using False by linarith
            subgoal using j_def prems two_pow_oe_n_as_halves by simp
            done
          then have "int (Nat_LSBF.to_nat ((z_filled @ z_consts) ! i) * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n =
              int (Nat_LSBF.to_nat (z_consts ! j) * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n"
            using length_z_filled nth_append_length_plus by metis
          also have "... = int (Nat_LSBF.to_nat (replicate (oe_n + 2 ^ n) False @ [True]) * 2 ^ (i * 2 ^ (n - 1))) mod int Fmr.n"
            unfolding z_consts_def using \<open>j < 2 ^ (oe_n - 1)\<close> by simp
          also have "... = int (2 ^ (oe_n + 2 ^ n)) * 2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n"
            by simp
          also have "... = z' i * 2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n"
            unfolding z'_def using False by simp
          also have "... = z' i \<otimes>\<^bsub>Fm\<^esub> (2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n)"
            by (simp add: mod_mult_right_eq Fmr.res_mult_eq)
          also have "2 ^ (i * 2 ^ (n - 1)) mod int Fmr.n = 2 [^]\<^bsub>Fm\<^esub> (i * 2 ^ (n - 1))"
            by (rule Fmr.pow_nat_eq[symmetric])
          finally show ?thesis .
        qed
        done
      finally show ?thesis .
    qed

    have "Fmr.to_residue_ring result = Fmr.to_residue_ring a \<otimes>\<^bsub>Fm\<^esub> Fmr.to_residue_ring b"
      using result_value result0 by argo

    moreover have "result \<in> Fmr.fermat_non_unique_carrier"
      unfolding result_def
      by (rule Fmr.from_nat_lsbf_correct(1))
    
    ultimately show ?thesis
      unfolding result_eq Fm_def int_lsbf_fermat.Fn_def by simp
  qed
qed

subsection "Schoenhage-Strassen Multiplication in $\\mathbb{N}$"

text "In order to multiply $a$ and $b$ (given in LSBF representation), find an $m$ s.t. $a \\cdot b < F_m$."
text "It suffices to just pick @{term \<open>m = max (bitsize (length a)) (bitsize (length b)) + 1\<close>}."
definition schoenhage_strassen_mul where
"schoenhage_strassen_mul a b = (let m = max (bitsize (length a)) (bitsize (length b)) + 1 in
  int_lsbf_fermat.reduce m (schoenhage_strassen m (fill (2 ^ (m + 1)) a) (fill (2 ^ (m + 1)) b))
)"

locale schoenhage_strassen_mul_context =
  fixes a b :: nat_lsbf
begin

definition bits_a where "bits_a = bitsize (length a)"
definition bits_b where "bits_b = bitsize (length b)"
definition m' where "m' = max bits_a bits_b"
definition m where "m = m' + 1"
definition car_len where "car_len = (2::nat) ^ (m + 1)"
definition fill_a where "fill_a = fill car_len a"
definition fill_b where "fill_b = fill car_len b"
definition fm_result where "fm_result = schoenhage_strassen m fill_a fill_b"

lemmas defs = bits_a_def bits_b_def m'_def m_def car_len_def fill_a_def fill_b_def

lemma
  shows length_a: "length a < 2 ^ (m - 1)"
    and length_b: "length b < 2 ^ (m - 1)"
  using m_def bitsize_length defs by fastforce+

lemma
  shows length_a': "length a \<le> 2 ^ (m + 1)"
    and length_b': "length b \<le> 2 ^ (m + 1)"
  using length_a length_b by (simp_all add: m_def nat_le_real_less nat_less_real_le)

lemma length_fill_a: "length fill_a = 2 ^ (m + 1)"
  unfolding fill_a_def car_len_def
  by (intro length_fill length_a')

lemma length_fill_b: "length fill_b = 2 ^ (m + 1)"
  unfolding fill_b_def car_len_def
  by (intro length_fill length_b')

sublocale fm: int_lsbf_fermat m .

definition Fm where "Fm = residue_ring (int_lsbf_fermat.n m)"
sublocale Fmr: residues fm.n "Fm"
  rewrites fm_Fm: "fm.Fn \<equiv> Fm"
  unfolding Fm_def fm.Fn_def by (rule fm.residues_axioms reflexive)+

lemma fill_a_carrier[simp, intro]: "fill_a \<in> fm.fermat_non_unique_carrier"
  by (intro fm.fermat_non_unique_carrierI length_fill_a)
lemma fill_b_carrier[simp, intro]: "fill_b \<in> fm.fermat_non_unique_carrier"
  by (intro fm.fermat_non_unique_carrierI length_fill_b)

lemma fm_result_carrier[simp, intro]: "fm_result \<in> fm.fermat_non_unique_carrier"
  unfolding fm_result_def
  by (intro conjunct2[OF schoenhage_strassen_correct'] fill_a_carrier fill_b_carrier)

lemma ssc': "fm.to_residue_ring fm_result = fm.to_residue_ring fill_a \<otimes>\<^bsub>Fm\<^esub> fm.to_residue_ring fill_b"
and "fm_result \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  unfolding atomize_conj fm_result_def fm_Fm[symmetric]
  by (intro schoenhage_strassen_correct' fill_a_carrier fill_b_carrier)

end

theorem schoenhage_strassen_mul_correct: "Nat_LSBF.to_nat (schoenhage_strassen_mul a b) = Nat_LSBF.to_nat a * Nat_LSBF.to_nat b"
proof -
  interpret schoenhage_strassen_mul_context a b .

  have "int (Nat_LSBF.to_nat a) * int (Nat_LSBF.to_nat b) < int_lsbf_fermat.n m"
  proof -
    have "Nat_LSBF.to_nat a < 2 ^ length a" "Nat_LSBF.to_nat b < 2 ^ length b" by (intro to_nat_length_bound)+
    moreover have "(2::nat) ^ length a < 2 ^ 2 ^ (m - 1)" "(2::nat) ^ length b < 2 ^ 2 ^ (m - 1)"
      using length_a length_b by simp_all
    ultimately have "Nat_LSBF.to_nat a * Nat_LSBF.to_nat b < 2 ^ 2 ^ (m - 1) * 2 ^ 2 ^ (m - 1)"
      by (metis bot_nat_0.extremum max.absorb3 max_less_iff_conj mult_strict_mono pos2 zero_less_power)
    also have "... = 2 ^ 2 ^ m" by (simp add: power2_eq_square power_even_eq m_def)
    finally show ?thesis by (simp add: nat_int_comparison(2))
  qed
  then have "int_lsbf_fermat.to_residue_ring m a \<otimes>\<^bsub>Fm\<^esub> int_lsbf_fermat.to_residue_ring m b =
      int (Nat_LSBF.to_nat a) * int (Nat_LSBF.to_nat b)"
    by (simp add: Fmr.res_mult_eq int_lsbf_fermat.to_residue_ring.simps mod_mult_eq)
  also have "int_lsbf_fermat.to_residue_ring m a = int_lsbf_fermat.to_residue_ring m fill_a"
    unfolding int_lsbf_fermat.to_residue_ring.simps defs by simp
  also have "int_lsbf_fermat.to_residue_ring m b = int_lsbf_fermat.to_residue_ring m fill_b"
    unfolding int_lsbf_fermat.to_residue_ring.simps defs by simp
  finally have c: "int_lsbf_fermat.to_residue_ring m fill_a \<otimes>\<^bsub>Fm\<^esub> int_lsbf_fermat.to_residue_ring m fill_b =
      int (Nat_LSBF.to_nat a) * int (Nat_LSBF.to_nat b)" .

  have "schoenhage_strassen_mul a b = int_lsbf_fermat.reduce m (schoenhage_strassen m fill_a fill_b)"
    by (simp only: schoenhage_strassen_mul_def Let_def defs)
  then have "Nat_LSBF.to_nat (schoenhage_strassen_mul a b) = Nat_LSBF.to_nat (schoenhage_strassen m fill_a fill_b) mod int_lsbf_fermat.n m"
    using fm.reduce_correct[OF fm_result_carrier] fm_result_def by algebra
  also have "... = nat (int (Nat_LSBF.to_nat (schoenhage_strassen m fill_a fill_b) mod int_lsbf_fermat.n m))"
    by simp
  also have "... = nat (int_lsbf_fermat.to_residue_ring m (schoenhage_strassen m fill_a fill_b))"
    unfolding int_lsbf_fermat.to_residue_ring.simps
    by (intro arg_cong[where f = nat] zmod_int)
  also have "... = nat (
    int_lsbf_fermat.to_residue_ring m fill_a \<otimes>\<^bsub>Fm\<^esub>
    int_lsbf_fermat.to_residue_ring m fill_b)"
    apply (intro arg_cong[where f = nat]) using ssc' unfolding fm_result_def .
  also have "... = nat (int (Nat_LSBF.to_nat a) * int (Nat_LSBF.to_nat b))"
    by (intro arg_cong[where f = nat] c)
  also have "... = Nat_LSBF.to_nat a * Nat_LSBF.to_nat b"
    by (simp add: nat_mult_distrib)
  finally show ?thesis .
qed

end