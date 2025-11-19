theory Tau_Reduction
  imports Bit_Counting Utils
begin 

subsection \<open>Expressing the bit counting function with a binomial coefficient\<close>

locale Tau_Reduction = 
  fixes N::nat and S::nat and T::nat
  assumes HN: "is_power2 (int N)" 
      and HS: "S < N" 
      and HT: "T < N"
begin
 
abbreviation \<sigma> where "\<sigma> \<equiv> count_bits"
abbreviation \<tau> where "\<tau> \<equiv> count_carries"

definition R where "R \<equiv> (S+T+1)*N + T + 1"

text \<open>We prove an identity on natural numbers. 
  To make it more tractable we transpose it to integers.\<close>
lemma rewrite_R:
  "N^2 * (S+T) + N * (N-1-S) + (N-1-T) = (N-1) * R"
proof -
  let ?iS = "int S" and ?iT = "int T" and ?iN = "int N"

  have "int (N*N * (S+T) + N * (N-1-S) + (N-1-T)) = 
    ?iN*?iN * (?iS+?iT) + ?iN * (?iN-1-?iS) + (?iN-1-?iT)"
    using HS HT int_ops by auto
  also have "... = (?iN-1)*((?iS+?iT+1) * ?iN + ?iT + 1)"
    by algebra
  also have "... = (?iN - 1) * int ((S+T+1) * N + T + 1)"
    using int_ops by presburger
  also have "... = int ((N-1) * ((S+T+1) * N + T + 1))"
    using HS HT int_ops
    by (metis (mono_tags, opaque_lifting) One_nat_def R_def Suc_leI diff_is_0_eq not_gr_zero 
       of_nat_diff verit_comp_simplify1(3) zero_diff)
   finally show ?thesis using R_def by (metis nat_int_comparison(1) power2_eq_square)
qed

text \<open>This is a direct consequence of the properties of sigma and tau.\<close>
text \<open>Lemma 1.4 in the article\<close>
lemma tau_as_binomial_coefficient:
  "\<tau> S T = 0 \<longleftrightarrow> N^2 dvd 2 * (N-1) * R choose (N-1) * R"
proof -
  from HN obtain n where n_def: "N = 2^n" unfolding is_power2_def by auto
  
  have 1: "N-1-S < N" using HS by auto
  have 2: "N-1-T < N" using HT by auto
  
  have "N * (N-1-S) + (N-1-T) < N * (N-1) + N" 
    using 1 2
    by (meson add_mono_thms_linordered_field(4) diff_le_self mult_le_mono2)
  also have "... = N^2" 
    by (simp add: algebra_simps numeral_eq_Suc)
  finally have 3: "N * (N-1-S) + (N-1-T) < N^2" .
  
  have "\<tau> S T = 0 \<longleftrightarrow> \<sigma> S + \<sigma> T - \<sigma> (S+T) = 0" 
    using count_carries_def_alt by simp
  also have "... \<longleftrightarrow> \<sigma> S + \<sigma> T \<le> \<sigma> (S+T)" 
    by auto
  also have "... \<longleftrightarrow> (\<sigma> S + \<sigma> (N-1-S)) + (\<sigma> T + \<sigma> (N-1-T)) \<le> \<sigma> (S+T) + \<sigma> (N-1-S) + \<sigma> (N-1-T)"
    by auto 
  also have "... \<longleftrightarrow> 2 * \<sigma> (N-1) \<le> \<sigma> (S+T) + \<sigma> (N-1-T) + \<sigma> (N-1-S)"
    using HS HT count_bits_complement count_bits_bounded n_def by auto 
  also have "... \<longleftrightarrow> 2 * n \<le> \<sigma> (S+T) + \<sigma> (N-1-T) + \<sigma> (N-1-S)"
    using count_bits_block_ones n_def by simp
  also have "... \<longleftrightarrow> 2 * n \<le> \<sigma> (S+T) + \<sigma> (N * (N-1-S) + (N-1-T))"
    using count_bits_add_shift 2 n_def
    by (smt (verit, best) add.commute add.left_commute mult.commute)
  also have "... \<longleftrightarrow> 2 * n \<le> \<sigma> (N^2 * (S+T) + N * (N-1-S) + (N-1-T))"
    using count_bits_add_shift 3 n_def  
    by (smt (verit) add.assoc add.commute mult.commute power_mult)
  also have "... \<longleftrightarrow> 2 * n \<le> \<sigma> ((N-1) * R)"
    using rewrite_R HS HT by simp
  also have "... \<longleftrightarrow> N^2 dvd 2 * (N-1) * R choose (N-1) * R"
    using count_bits_divibility_binomial n_def
    by (metis distrib_right mult_2 mult_2_right power_mult)
  finally show ?thesis .
qed

end

end