section "Frequency Moments"

theory Frequency_Moments
  imports 
    Frequency_Moments_Preliminary_Results
    Universal_Hash_Families.Universal_Hash_Families_More_Finite_Fields
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities
begin

text \<open>This section contains a definition of the frequency moments of a stream and a few general results about 
frequency moments..\<close>

definition F where
  "F k xs = (\<Sum> x \<in> set xs. (rat_of_nat (count_list xs x)^k))"

lemma F_ge_0: "F k as \<ge> 0"
  unfolding F_def by (rule sum_nonneg, simp)

lemma F_gr_0:
  assumes "as \<noteq> []"
  shows "F k as > 0"
proof -
  have "rat_of_nat 1 \<le> rat_of_nat (card (set as))"
    using assms card_0_eq[where A="set as"] 
    by (intro of_nat_mono)
     (metis List.finite_set One_nat_def Suc_leI neq0_conv set_empty)
  also have "... = (\<Sum>x\<in>set as. 1)" by simp
  also have "... \<le> (\<Sum>x\<in>set as. rat_of_nat (count_list as x) ^ k)"
    by (intro sum_mono one_le_power)
     (metis  count_list_gr_1  of_nat_1 of_nat_le_iff)
  also have "... \<le> F k as"
    by (simp add:F_def)
  finally show ?thesis by simp
qed

definition P\<^sub>e :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool list option" where
  "P\<^sub>e p n f = (if p > 1 \<and> f \<in> bounded_degree_polynomials (mod_ring p) n then
    ([0..<n] \<rightarrow>\<^sub>e Nb\<^sub>e p) (\<lambda>i \<in> {..<n}. ring.coeff (mod_ring p) f i) else None)"

lemma poly_encoding:
  "is_encoding (P\<^sub>e p n)"
proof (cases "p > 1")
  case True
  interpret cring "mod_ring p"
    using mod_ring_is_cring True by blast
  have a:"inj_on (\<lambda>x. (\<lambda>i \<in> {..<n}. (coeff x i))) (bounded_degree_polynomials (mod_ring p) n)"
  proof (rule inj_onI)
    fix x y
    assume b:"x \<in> bounded_degree_polynomials (mod_ring p) n"
    assume c:"y \<in> bounded_degree_polynomials (mod_ring p) n"
    assume d:"restrict (coeff x) {..<n} = restrict (coeff y) {..<n}"
    have "coeff x i = coeff y i" for i
    proof (cases "i < n")
      case True
      then show ?thesis by (metis lessThan_iff restrict_apply d)
    next
      case False
      hence e: "i \<ge> n" by linarith
      have "coeff x i = \<zero>\<^bsub>mod_ring p\<^esub>"
        using b e by (subst coeff_length, auto simp:bounded_degree_polynomials_length)
      also have "... = coeff y i"
        using c e by (subst coeff_length, auto simp:bounded_degree_polynomials_length)
      finally show ?thesis by simp
    qed
    then show "x = y"
      using b c univ_poly_carrier 
      by (subst coeff_iff_polynomial_cond) (auto simp:bounded_degree_polynomials_length) 
  qed

  have "is_encoding (\<lambda>f. P\<^sub>e p n f)"
    unfolding P\<^sub>e_def using a True
    by (intro encoding_compose[where f="([0..<n] \<rightarrow>\<^sub>e Nb\<^sub>e p)"] fun_encoding bounded_nat_encoding) 
     auto
  thus ?thesis by simp
next
  case False
  hence "is_encoding (\<lambda>f. P\<^sub>e p n f)"
    unfolding P\<^sub>e_def using encoding_triv by simp
  then show ?thesis by simp
qed

lemma bounded_degree_polynomial_bit_count:
  assumes "p > 1"
  assumes "x \<in> bounded_degree_polynomials (mod_ring p) n"
  shows "bit_count (P\<^sub>e p n x) \<le> ereal (real n * (log 2 p + 1))"
proof -
  interpret cring "mod_ring p"
    using mod_ring_is_cring assms by blast

  have a: "x \<in> carrier (poly_ring (mod_ring p))"
    using assms(2) by (simp add:bounded_degree_polynomials_def)

  have "real_of_int \<lfloor>log 2 (p-1)\<rfloor>+1 \<le> log 2 (p-1) + 1"
    using floor_eq_iff by (intro add_mono, auto) 
  also have "... \<le> log 2 p + 1"
    using assms by (intro add_mono, auto)
  finally have b: "\<lfloor>log 2 (p-1)\<rfloor>+1 \<le> log 2 p + 1"
    by simp

  have "bit_count (P\<^sub>e p n x) = (\<Sum> k \<leftarrow> [0..<n]. bit_count (Nb\<^sub>e p (coeff x k)))"
    using assms restrict_extensional 
    by (auto intro!:arg_cong[where f="sum_list"] simp add:P\<^sub>e_def fun_bit_count lessThan_atLeast0)
  also have "... = (\<Sum> k \<leftarrow> [0..<n]. ereal (floorlog 2 (p-1)))"
    using coeff_in_carrier[OF a] mod_ring_carr 
    by (subst bounded_nat_bit_count_2, auto)
  also have "... = n * ereal (floorlog 2 (p-1))"
    by (simp add: sum_list_triv)
  also have "... = n * real_of_int (\<lfloor>log 2 (p-1)\<rfloor>+1)" 
    using assms(1) by (simp add:floorlog_def)
  also have "... \<le> ereal (real n * (log 2 p + 1))" 
    by (subst ereal_less_eq, intro mult_left_mono b, auto)
  finally show ?thesis by simp
qed

end