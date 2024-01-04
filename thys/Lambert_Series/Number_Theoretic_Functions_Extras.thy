section \<open>Some Facts About Number-Theoretic Functions\<close>
theory Number_Theoretic_Functions_Extras
imports
  "Dirichlet_Series.Dirichlet_Series_Analysis"
  "Dirichlet_Series.Divisor_Count"
  Lambert_Series_Library
begin

lemma (in nat_power_field) nat_power_minus:
  "a \<noteq> 0 \<or> n \<noteq> 0 \<Longrightarrow> nat_power n (-a) = inverse (nat_power n a)"
  using nat_power_diff[of n 0 a] by (cases "n = 0") (simp_all add: field_simps)

lemma divisor_sigma_minus:
  fixes a :: "'a :: {nat_power_field, field_char_0}"
  shows "divisor_sigma (-a) n = divisor_sigma a n / nat_power n a"
proof (cases "n = 0")
  case n: False
  have "divisor_sigma (-a :: 'a) n = (\<Sum>d | d dvd n. nat_power d (-a))"
    by (simp add: divisor_sigma_def)
  also have "\<dots> = (\<Sum>d | d dvd n. nat_power d a / nat_power n a)"
    using n by (intro sum.reindex_bij_witness[of _ "\<lambda>d. n div d" "\<lambda>d. n div d"])
               (auto elim!: dvdE simp: field_simps nat_power_minus nat_power_mult_distrib)
  also have "\<dots> = divisor_sigma a n / nat_power n a"
    by (simp add: sum_divide_distrib divisor_sigma_def)
  finally show ?thesis .
qed auto

lemma norm_moebius_mu:
  "norm (moebius_mu n ::'a :: {real_normed_algebra_1, comm_ring_1}) = ind squarefree n"
  by (subst of_int_moebius_mu [symmetric], subst norm_of_int) (auto simp: abs_moebius_mu)



lemma conv_radius_nat_power: "conv_radius (\<lambda>n. nat_power n a :: 'a :: {nat_power_normed_field, banach}) = 1"
proof (rule tendsto_imp_conv_radius_eq)
  show "(\<lambda>n. ereal (norm (nat_power n a :: 'a) powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
  proof (rule Lim_transform_eventually)
    show "(\<lambda>n. ereal ((real n powr (a \<bullet> 1)) powr (1 / real n))) \<longlonglongrightarrow> ereal 1"
      by (rule tendsto_ereal) real_asymp
    show "eventually (\<lambda>n. (real n powr (a \<bullet> 1)) powr (1 / real n) =
            ereal (norm (nat_power n a :: 'a) powr (1 / real n))) at_top"
      using eventually_gt_at_top[of 0] by eventually_elim (simp add: norm_nat_power)
  qed
qed (simp_all add: one_ereal_def)

lemma not_convergent_liouville_lambda:
  "\<not>convergent (liouville_lambda :: nat \<Rightarrow> 'a :: {real_normed_algebra, comm_ring_1, semiring_char_0})"
proof -
  have "\<not>(liouville_lambda :: nat \<Rightarrow> 'a) \<longlonglongrightarrow> c" for c
  proof (rule oscillation_imp_not_tendsto)
    show "eventually (\<lambda>n. liouville_lambda (2 ^ (2 * n)) \<in> {1 :: 'a}) sequentially"
      by auto
    show "filterlim (\<lambda>n. 2 ^ (2 * n) :: nat) at_top sequentially"
      by real_asymp
    show "eventually (\<lambda>n. liouville_lambda (2 ^ (2 * n + 1)) \<in> {-1 :: 'a}) sequentially"
      by (subst liouville_lambda.power) auto
    show "filterlim (\<lambda>n. 2 ^ (2 * n + 1) :: nat) at_top sequentially"
      by real_asymp
  qed auto
  thus ?thesis
    by (auto simp: convergent_def)
qed  

lemma conv_radius_liouville_lambda:
  "conv_radius (liouville_lambda :: nat \<Rightarrow> 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (liouville_lambda :: nat \<Rightarrow> 'a)"
    using not_convergent_liouville_lambda[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  hence "conv_radius (liouville_lambda :: nat \<Rightarrow> 'a) \<le> norm (1 :: 'a)"
    by (intro conv_radius_leI') auto
  moreover have "conv_radius (liouville_lambda :: nat \<Rightarrow> 'a) \<ge> 1"
  proof (rule conv_radius_bigo_polynomial)
    show "(liouville_lambda :: nat \<Rightarrow> 'a) \<in> O(\<lambda>n. of_nat n ^ 0)"
      by (intro bigoI[of _ 1] eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto simp: liouville_lambda_def norm_power)
  qed
  ultimately show ?thesis
    by (intro antisym) (auto simp: one_ereal_def)
qed

lemma not_convergent_mangoldt: "\<not>convergent (mangoldt :: nat \<Rightarrow> 'a :: {real_normed_algebra_1})"
proof -
  have *: "\<not>primepow (6 * n :: nat)" for n
    by (rule not_primepowI[of 2 3]) auto
  have "\<not>(mangoldt :: nat \<Rightarrow> 'a) \<longlonglongrightarrow> c" for c
  proof (rule oscillation_imp_not_tendsto)
    show "eventually (\<lambda>n. mangoldt (2 ^ n) \<in> {of_real (ln 2) :: 'a}) sequentially"
      by (auto simp: mangoldt_primepow)
    show "filterlim (\<lambda>n. 2 ^ n :: nat) at_top sequentially"
      by real_asymp
    show "eventually (\<lambda>n. mangoldt (6 * n) \<in> {0 :: 'a}) sequentially"
      using * by (auto simp: mangoldt_def)
    show "filterlim (\<lambda>n. 6 * n :: nat) at_top sequentially"
      by real_asymp
  qed auto
  thus ?thesis
    by (auto simp: convergent_def)
qed  

lemma conv_radius_mangoldt:
  "conv_radius (mangoldt :: nat \<Rightarrow> 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (mangoldt :: nat \<Rightarrow> 'a)"
    using not_convergent_mangoldt[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  hence "conv_radius (mangoldt :: nat \<Rightarrow> 'a) \<le> norm (1 :: 'a)"
    by (intro conv_radius_leI') auto
  moreover have "conv_radius (mangoldt :: nat \<Rightarrow> 'a) \<ge> 1"
  proof (rule conv_radius_bigo_polynomial)
    have "(mangoldt :: nat \<Rightarrow> 'a) \<in> O(\<lambda>n. of_real (ln (real n)))"
      by (intro bigoI[of _ 1] eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto simp: mangoldt_le)
    also have "(\<lambda>n. of_real (ln (real n))) \<in> O(\<lambda>n. of_nat n :: 'a)"
      by (subst landau_o.big.norm_iff [symmetric], unfold norm_of_real norm_of_nat) real_asymp      
    finally show "(mangoldt :: nat \<Rightarrow> 'a) \<in> O(\<lambda>n. of_nat n ^ 1)"
      by simp
  qed
  ultimately show ?thesis
    by (intro antisym) (auto simp: one_ereal_def)
qed

lemma not_convergent_moebius_mu: "\<not>convergent (moebius_mu :: nat \<Rightarrow> 'a :: real_normed_field)"
proof (rule oscillation_imp_not_convergent)
  have "infinite {p. prime (p :: nat)}"
    by (rule primes_infinite)
  hence "frequently (prime :: nat \<Rightarrow> bool) cofinite"
    by (simp add: Inf_many_def)
  hence "frequently (\<lambda>n. moebius_mu n = (-1 :: 'a)) cofinite"
    by (rule frequently_elim1) (simp add: moebius_mu.prime)
  thus "frequently (\<lambda>n. moebius_mu n \<in> {(-1 :: 'a)}) sequentially"
    using cofinite_eq_sequentially by fastforce
next
  have "infinite (range (\<lambda>n. 4 * n :: nat))"
    by (subst finite_image_iff) (auto simp: inj_on_def)
  moreover {
    have "\<not>squarefree (2 ^ 2 :: nat)"
      by (subst squarefree_power_iff) auto
    also have "2 ^ 2 = (4 :: nat)"
      by simp
    finally have "range (\<lambda>n. 4 * n :: nat) \<subseteq> {n::nat. \<not>squarefree n}"
      by (auto dest: squarefree_multD)
  }
  ultimately have "frequently (\<lambda>n::nat. \<not>squarefree n) cofinite"
    unfolding INFM_iff_infinite using finite_subset by blast
  thus "\<exists>\<^sub>F n in sequentially. moebius_mu n \<in> {0}"
    unfolding cofinite_eq_sequentially by (rule frequently_elim1) auto
qed auto

lemma conv_radius_moebius_mu:
  "conv_radius (moebius_mu :: nat \<Rightarrow> 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (moebius_mu :: nat \<Rightarrow> 'a)"
    using not_convergent_moebius_mu[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  hence "conv_radius (moebius_mu :: nat \<Rightarrow> 'a) \<le> norm (1 :: 'a)"
    by (intro conv_radius_leI') auto
  moreover have "conv_radius (moebius_mu :: nat \<Rightarrow> 'a) \<ge> conv_radius (\<lambda>_. 1 :: 'a)"
    by (intro conv_radius_mono always_eventually) (auto simp: norm_moebius_mu ind_def)
  ultimately show ?thesis
    by (intro antisym) (auto simp: one_ereal_def)
qed

lemma not_convergent_totient:
  "\<not>convergent (\<lambda>n. of_nat (totient n) :: 'a :: {real_normed_field, banach})"
proof
  assume "convergent (\<lambda>n. of_nat (totient n) :: 'a)"
  then obtain L where L: "eventually (\<lambda>n. totient n = L) at_top"
    by (auto simp: convergent_def filterlim_of_nat_iff)
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> totient n = L"
    unfolding eventually_at_top_linorder by blast
  obtain p q where "prime p" "p > N" "prime q" "q > p"
    using bigger_prime by blast
  with N[of p] N[of q] show False
    by (auto simp: totient_prime)
qed

lemma conv_radius_totient:
  "conv_radius (\<lambda>n. of_nat (totient n) :: 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (\<lambda>n. of_nat (totient n) :: 'a)"
    using not_convergent_totient[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  hence "conv_radius (\<lambda>n. of_nat (totient n) :: 'a) \<le> norm (1 :: 'a)"
    by (intro conv_radius_leI') auto
  moreover have "conv_radius (\<lambda>n. of_nat (totient n) :: 'a) \<ge> 1"
  proof (rule conv_radius_bigo_polynomial)
    show "(\<lambda>n. of_nat (totient n)) \<in> O(\<lambda>n. of_nat n ^ 1)"
      by (intro bigoI[of _ 1] always_eventually) (auto simp: totient_le)
  qed
  ultimately show ?thesis
    by (intro antisym) (auto simp: one_ereal_def)
qed

end