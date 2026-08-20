theory Erdos_Ginzburg_Ziv
  imports
    EGZ_Prime
    "HOL-Computational_Algebra.Primes"
begin

section \<open>The full Erd\H{o}s-Ginzburg-Ziv theorem\<close>

text \<open>
  The composite-modulus case is obtained from the prime case by strong
  induction. Writing @{term n} as @{text "m * p"} with @{term p} prime, we
  repeatedly extract @{term p}-element zero-sum blocks, divide their sums by
  @{term p}, and apply the induction hypothesis to the resulting multiset of
  quotients.
\<close>

subsection \<open>Auxiliary multiset decompositions\<close>

lemma exists_submultiset_of_size:
  fixes M :: "'a::linorder multiset"
  assumes n_le: "n \<le> size M"
  shows "\<exists>N. N \<subseteq># M \<and> size N = n"
proof -
  let ?xs = "sorted_list_of_multiset M"
  let ?N = "mset (take n ?xs)"
  have N_sub: "?N \<subseteq># M"
    by (metis mset_nths_subseteq mset_sorted_list_of_multiset nths_upt_eq_take)
  have N_size: "size ?N = n"
  proof -
    have xs_len: "size M = length ?xs"
      by (metis mset_sorted_list_of_multiset size_mset)
    then show ?thesis
      using n_le by auto
  qed
  show ?thesis
    using N_sub N_size by (intro exI[of _ ?N]) simp
qed

lemma union_blocks_size:
  fixes Bs :: "'a multiset multiset"
  assumes blocks_size: "\<forall>B\<in>#Bs. size B = n"
  shows "size (sum_mset Bs) = size Bs * n"
  using blocks_size
by (induction Bs) auto

lemma union_blocks_div_sum:
  assumes blocks_div: "\<forall>B\<in>#Bs. sum_mset B mod int p = 0"
  shows "sum_mset (sum_mset Bs) = int p * sum_mset (image_mset (\<lambda>B. sum_mset B div int p) Bs)"
  using blocks_div
proof (induction Bs)
  case empty
  then show ?case
    by simp
next
  case (add B Bs)
  have B_div: "sum_mset B mod int p = 0"
    using add.prems by simp
  have rest_div: "\<forall>C\<in>#Bs. sum_mset C mod int p = 0"
    using add.prems by auto
  have B_eq: "sum_mset B = int p * (sum_mset B div int p)"
    using div_mult_mod_eq[of "sum_mset B" "int p"] B_div by (simp add: mult.commute)
  have "sum_mset (sum_mset (add_mset B Bs)) = sum_mset B + sum_mset (sum_mset Bs)"
    by simp
  also have "\<dots> = int p * (sum_mset B div int p) + int p * sum_mset (image_mset (\<lambda>B. sum_mset B div int p) Bs)"
    using B_eq add.IH[OF rest_div] by simp
  also have "\<dots> = int p * (sum_mset B div int p + sum_mset (image_mset (\<lambda>B. sum_mset B div int p) Bs))"
    by (simp add: algebra_simps)
  also have "\<dots> = int p * sum_mset (image_mset (\<lambda>B. sum_mset B div int p) (add_mset B Bs))"
    by simp
  finally show ?case .
qed

lemma extract_prime_blocks:
  assumes prime_p: "prime p"
  assumes size_M: "size M = k * p + (p - 1)"
  shows "\<exists>Bs R. M = sum_mset Bs + R \<and> size Bs = k \<and> size R = p - 1 \<and>
    (\<forall>B\<in>#Bs. size B = p \<and> sum_mset B mod int p = 0)"
  using assms
proof (induction k arbitrary: M)
  case 0
  then show ?case
    by (intro exI[of _ "{#}"] exI[of _ M]) simp
next
  case (Suc k)
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF Suc.prems(1)] .
  have size_ge: "2 * p - 1 \<le> size M"
  proof -
    have p_le: "p \<le> Suc k * p"
      using p_pos by simp
    have "2 * p - 1 = p + (p - 1)"
      using p_pos by arith
    then show ?thesis
      using Suc.prems(2) p_le by arith
  qed
  from exists_submultiset_of_size[OF size_ge]
  obtain M0 where M0_sub: "M0 \<subseteq># M" and size_M0: "size M0 = 2 * p - 1"
    by auto
  from prime_egz[OF Suc.prems(1) size_M0]
  obtain B where B_sub0: "B \<subseteq># M0" and B_size: "size B = p" and B_sum: "sum_mset B mod int p = 0"
    by auto
  have B_sub: "B \<subseteq># M"
    using B_sub0 M0_sub by auto
  have rem_size: "size (M - B) = k * p + (p - 1)"
  proof -
    have MB: "M = B + (M - B)"
      using B_sub by simp
    have "size M = size (B + (M - B))"
      using MB by simp
    also have "\<dots> = size B + size (M - B)"
      by simp
    finally have "size M = size B + size (M - B)" .
    then have "size (M - B) = size M - size B"
      using B_sub by simp
    then show ?thesis
      using Suc.prems(2) B_size by simp
  qed
  from Suc.IH[OF Suc.prems(1) rem_size]
  obtain Bs R where rem_split: "M - B = sum_mset Bs + R"
    and Bs_size: "size Bs = k"
    and R_size: "size R = p - 1"
    and Bs_good: "\<forall>C\<in>#Bs. size C = p \<and> sum_mset C mod int p = 0"
    by auto
  let ?Bs = "add_mset B Bs"
  have M_split: "M = sum_mset ?Bs + R"
    using B_sub rem_split subset_mset.add_diff_inverse by fastforce
  have Bs_all_good: "\<forall>C\<in>#?Bs. size C = p \<and> sum_mset C mod int p = 0"
    using B_size B_sum Bs_good by auto
  show ?case
    using M_split Bs_size R_size Bs_all_good
    by (intro exI[of _ ?Bs] exI[of _ R]) simp
qed

subsection \<open>Strong induction on the modulus\<close>

text \<open>
  The prime branch is handled directly by @{thm [source] prime_egz}. For a
  composite modulus @{term n}, the previous lemma extracts @{text "2 * m - 1"}
  prime-sized blocks with sums divisible by @{term p}. Applying the induction
  hypothesis to the block sums divided by @{term p} selects enough blocks whose
  union has size @{term n} and total sum divisible by @{term n}.
\<close>

theorem erdos_ginzburg_ziv_exact:
  assumes n_pos: "0 < n"
  assumes size_M: "size M = 2 * n - 1"
  shows "\<exists>N. N \<subseteq># M \<and> size N = n \<and> sum_mset N mod int n = 0"
  using n_pos size_M
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  have n_pos: "0 < n"
    using less.prems(1) .
  have size_M: "size M = 2 * n - 1"
    using less.prems(2) .
  show ?case
  proof (cases "n = 1")
    case True
    then show ?thesis
      using n_pos size_M by (intro exI[of _ M]) auto
  next
    case False
    then have n_gt1: "1 < n"
      using n_pos by simp
    show ?thesis
    proof (cases "prime n")
      case True
      then show ?thesis
        using prime_egz[OF True size_M] by simp
    next
      case False
      from prime_factor_nat[of n] n_gt1
      obtain p where prime_p: "prime p" and p_dvd: "p dvd n"
        by auto
      have p_pos: "0 < p"
        using prime_gt_0_nat[OF prime_p] .
      define m where "m = n div p"
      have n_eq: "n = m * p"
        using p_dvd p_pos by (simp add: m_def mult.commute)
      have m_pos: "0 < m"
        using n_eq n_pos by auto
      have m_lt_n: "m < n"
        by (simp add: m_pos n_eq prime_gt_Suc_0_nat prime_p)
      have blocks_size_eq: "size M = (2 * m - 1) * p + (p - 1)"
      proof -
        have "size M = 2 * (m * p) - 1"
          using size_M n_eq by simp
        also have "\<dots> = ((2 * m - 1) + 1) * p - 1"
          using m_pos by (simp add: algebra_simps)
        also have "\<dots> = (2 * m - 1) * p + (p - 1)"
          using p_pos by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      from extract_prime_blocks[OF prime_p blocks_size_eq]
      obtain Bs R where M_split: "M = sum_mset Bs + R"
        and Bs_size: "size Bs = 2 * m - 1"
        and R_size: "size R = p - 1"
        and Bs_good: "\<forall>B\<in>#Bs. size B = p \<and> sum_mset B mod int p = 0"
        by auto
      let ?f = "\<lambda>B. sum_mset B div int p"
      let ?Sums = "image_mset ?f Bs"
      have sums_size: "size ?Sums = 2 * m - 1"
        using Bs_size by simp
      from less.IH[OF m_lt_n, of ?Sums] m_pos sums_size
      obtain S where S_sub: "S \<subseteq># ?Sums"
        and S_size: "size S = m"
        and S_sum: "sum_mset S mod int m = 0"
        by auto
      obtain C where sums_split: "?Sums = S + C"
        using S_sub by (auto simp: subset_mset.le_iff_add)
      from image_mset_eq_plusD[OF sums_split]
      obtain Bs1 Bs2 where Bs_split: "Bs = Bs1 + Bs2"
        and S_image: "S = image_mset ?f Bs1"
        and C_image: "C = image_mset ?f Bs2"
        by auto
      have Bs1_size: "size Bs1 = m"
        using S_size S_image by simp
      have Bs1_good: "\<forall>B\<in>#Bs1. size B = p \<and> sum_mset B mod int p = 0"
        using Bs_good Bs_split by auto
      have N_sub: "sum_mset Bs1 \<subseteq># M"
        by (simp add: Bs_split M_split)
      have N_size: "size (sum_mset Bs1) = n"
        using Bs1_good Bs1_size n_eq union_blocks_size by blast
      have N_sum: "sum_mset (sum_mset Bs1) mod int n = 0"
      proof -
        have Bs1_div: "\<forall>B\<in>#Bs1. sum_mset B mod int p = 0"
          using Bs1_good by auto
        have sums_mod: "sum_mset (image_mset ?f Bs1) mod int m = 0"
          using S_sum S_image by simp
        have total_eq: "sum_mset (sum_mset Bs1) = int p * sum_mset (image_mset ?f Bs1)"
          by (rule union_blocks_div_sum[OF Bs1_div])
        have m_dvd: "int m dvd sum_mset (image_mset ?f Bs1)"
          using sums_mod by (simp add: dvd_eq_mod_eq_0)
        then obtain t where t_eq: "sum_mset (image_mset ?f Bs1) = int m * t"
          by auto
        have "sum_mset (sum_mset Bs1) = int n * t"
          using total_eq t_eq n_eq by (simp add: algebra_simps)
        then show ?thesis
          by simp
      qed
      show ?thesis
        using N_sub N_size N_sum by (intro exI[of _ "sum_mset Bs1"]) simp
    qed
  qed
qed

subsection \<open>The monotone cardinality form\<close>

theorem erdos_ginzburg_ziv:
  assumes n_pos: "0 < n"
  assumes size_M: "size M \<ge> 2 * n - 1"
  shows "\<exists>N. N \<subseteq># M \<and> size N = n \<and> sum_mset N mod int n = 0"
proof -
  from exists_submultiset_of_size[of "2 * n - 1" M] size_M
  obtain M0 where M0_sub: "M0 \<subseteq># M" and M0_size: "size M0 = 2 * n - 1"
    by auto
  from erdos_ginzburg_ziv_exact[OF n_pos M0_size]
  obtain N where N_sub0: "N \<subseteq># M0" and N_size: "size N = n" and N_sum: "sum_mset N mod int n = 0"
    by auto
  have N_sub: "N \<subseteq># M"
    using N_sub0 M0_sub by auto
  show ?thesis
    using N_sub N_size N_sum by (intro exI[of _ N]) simp
qed

end

