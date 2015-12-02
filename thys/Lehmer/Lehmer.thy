theory Lehmer
imports
  Main
  Multiplicative_Group
begin

section {* Lehmer's Theorem *}
text_raw {* \label{sec:lehmer} *}

text {*
  In this section we prove Lehmer's Theorem~\cite{lehmer1927fermat_converse} and its converse.
  These two theorems characterize a necessary and complete criterion for primality. This criterion
  is the basis of the Lucas-Lehmer primality test and the primality certificates of
  Pratt~\cite{pratt1975certificate}.
*}

lemma coprime_power_nat:
  fixes a b :: nat assumes "0 < n" shows "coprime a (b ^ n) \<longleftrightarrow> coprime a b"
  using assms
proof (induct n)
  case (Suc n) then show ?case
    by (cases n) (simp_all add: coprime_mul_eq_nat del: One_nat_def)
qed simp

lemma mod_1_coprime_nat:
  fixes a b :: nat assumes "0 < n" "[a ^ n = 1] (mod b)" shows "coprime a b"
proof -
  from assms have "coprime (a ^ n) b" by (simp cong: cong_gcd_eq_nat)
  with `0 < n` show ?thesis
    by (simp add: coprime_power_nat gcd_commute_nat del: One_nat_def)
qed

lemma phi_leq: "phi x \<le> nat x - 1"
proof -
  have "phi x \<le> card {1..x - 1}"
    unfolding phi_def by (rule card_mono) auto
  then show ?thesis by simp
qed

lemma phi_nonzero:
  assumes "2 \<le> x" shows "phi x \<noteq> 0"
proof -
  have "coprime ((x - 1) + 1) (x - 1)"
    by (simp only: coprime_plus_one_int)
  with assms have "card {x - 1} \<le> phi x"
    unfolding phi_def by (intro card_mono bounded_set1_int) (simp add: gcd_commute_int)
    (* XXX: We need bounded_set1_int here because of the finite_Collect simproc) *)
  then show ?thesis by auto
qed

text {*
  This is a weak variant of Lehmer's theorem: All numbers less then @{term "p - 1 :: nat"}
  must be considered.
*}

lemma lehmers_weak_theorem:
  assumes "2 \<le> p"
  assumes min_cong1: "\<And>x. 0 < x \<Longrightarrow> x < p - 1 \<Longrightarrow> [a ^ x \<noteq> 1] (mod p)"
  assumes cong1: "[a ^ (p - 1) = 1] (mod p)"
  shows "prime p"
proof -
  from `2 \<le> p` cong1 have "coprime a p"
    by (intro mod_1_coprime_nat[of "p - 1"]) auto
  then have "[a ^ phi (int p) = 1] (mod p)"
    by (intro euler_theorem[transferred]) auto
  then have "phi (int p) \<ge> p - 1 \<or> phi (int p) = 0"
    using min_cong1[of "phi (int p)"] by fastforce
  then show "prime p" using phi_leq[transferred, of p] phi_nonzero `2 \<le> p`
    by (auto intro: prime_phi)
qed

lemma prime_factors_elem:
  fixes n :: nat assumes "1 < n" shows "\<exists>p. p \<in> prime_factors n"
  using assms by (cases "prime n") (auto simp: prime_factors_altdef2_nat prime_factor_nat)

lemma prime_factors_dvd_nat:
  fixes p :: nat assumes "x \<in> prime_factors p" shows "x dvd p"
  using assms by (cases "0 < p") (auto simp: prime_factors_altdef2_nat)

lemma cong_pow_1_nat:
  fixes a b :: nat assumes "[a = 1] (mod b)" shows "[a ^ x = 1] (mod b)"
by (metis assms cong_exp_nat power_one)

lemma cong_gcd_eq_1_nat:
  fixes a b :: nat
  assumes "0 < m" and cong_props: "[a ^ m = 1] (mod b)" "[a ^ n = 1] (mod b)"
  shows "[a ^ gcd m n = 1] (mod b)"
proof -
  obtain c d where gcd: "m * c = n * d + gcd m n" using bezout_nat[of m n] `0 < m`
    by auto
  have cong_m: "[a ^ (m * c) = 1] (mod b)" and cong_n: "[a ^ (n * d) = 1] (mod b)"
    using cong_props by (simp_all only: cong_pow_1_nat power_mult)
  have "[1 * a ^ gcd m n = a ^ (n * d) * a ^ gcd m n] (mod b)"
    using cong_n[simplified cong_sym_eq_nat] by (simp only: power_one cong_scalar_nat)
  also have "[a ^ (n * d) * a ^ gcd m n = a ^ (m * c)] (mod b)"
    using gcd by (simp add: power_add)
  also have "[a ^ (m * c) = 1] (mod b)" using cong_m by simp
  finally show "[a ^ gcd m n = 1] (mod b)" by simp
qed

lemma One_leq_div:
  fixes a b :: nat assumes "a dvd b" "a < b" shows "1 < b div a"
by (metis assms dvd_mult_div_cancel gr_implies_not0 less_Suc0 linorder_not_le mult_1_right
  mult_zero_right nat_1 order_le_neq_trans order_refl transfer_nat_int_numerals(2))

theorem lehmers_theorem:
  assumes "2 \<le> p"
  assumes pf_notcong1: "\<And>x. x \<in> prime_factors (p - 1) \<Longrightarrow> [a ^ ((p - 1) div x) \<noteq> 1] (mod p)"
  assumes cong1: "[a ^ (p - 1) = 1] (mod p)"
  shows "prime p"
proof cases
  assume "[a = 1] (mod p)" with `2 \<le>p` pf_notcong1 show ?thesis
    by (metis cong_pow_1_nat less_diff_conv linorder_neqE_nat linorder_not_less
      one_add_one prime_factors_elem two_is_prime_nat)
next
  assume A_notcong_1: "[a \<noteq> 1] (mod p)"
  { fix x assume "0 < x" "x < p - 1"
    have "[a ^ x \<noteq> 1] (mod p)"
    proof
      assume "[a ^ x = 1] (mod p)"
      then have gcd_cong_1: "[a ^ gcd x (p - 1) = 1] (mod p)"
        by (rule cong_gcd_eq_1_nat[OF `0 < x` _ cong1])

      have "gcd x (p - 1) = p - 1"
      proof (rule ccontr)
        assume "\<not>?thesis"
        then have gcd_p1: "gcd x (p - 1) dvd (p - 1)" "gcd x (p - 1) < p - 1"
          using gcd_le2_nat[of "p - 1" x] `2 \<le> p` by (simp, linarith)

        def c \<equiv> "(p - 1) div (gcd x (p - 1))"
        then have p_1_eq: "p - 1 = gcd x (p - 1) * c" unfolding c_def using gcd_p1
          by (metis dvd_mult_div_cancel)

        from gcd_p1 have "1 < c" unfolding c_def by (rule One_leq_div)
        then obtain q where q_pf: "q \<in> prime_factors c"
          using prime_factors_elem by auto
        then have "q dvd c" by (auto simp: prime_factors_dvd_nat)

        have "q \<in> prime_factors (p - 1)" using q_pf `1 < c` `2 \<le> p`
          by (subst p_1_eq) (simp add: prime_factors_product_nat)
        moreover
        have "[a ^ ((p - 1) div q) = 1] (mod p)"
          by (subst p_1_eq,subst dvd_div_mult_self[OF `q dvd c`,symmetric])
             (simp del: One_nat_def add: power_mult gcd_cong_1 cong_pow_1_nat)
        ultimately
        show False using pf_notcong1 by metis
      qed
      then show False using `x < p - 1`
        by (metis `0 < x` gcd_le1_nat gr_implies_not0 linorder_not_less)
    qed
  }
  with lehmers_weak_theorem[OF `2 \<le> p` _ cong1] show ?thesis by metis
qed

text {*
  The converse of Lehmer's theorem is also true.
*}

lemma converse_lehmer_weak:
 assumes prime_p:"prime p"
 shows "\<exists> a. [a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))
             \<and> a > 0 \<and> a < p"
 proof -
   have "p \<ge> 2" by (rule prime_ge_2_nat[OF prime_p])
   obtain a where a:"a \<in> {1 .. p - 1} \<and> {1 .. p - 1} = {a^i mod p | i . i \<in> UNIV}"
    using residue_prime_mult_group_has_gen[OF prime_p] by blast
  {
   { fix x::nat assume x:"0 < x \<and> x \<le> p - 2 \<and> [a^x = 1] (mod p)"
     have "{a^i mod p| i. i \<in> UNIV} = {a^i mod p | i. 0 < i \<and> i \<le> x}"
     proof
      show "{a ^ i mod p | i. 0 < i \<and> i \<le> x} \<subseteq> {a ^ i mod p | i. i \<in> UNIV}" by blast
      { fix y assume y:"y \<in> {a^i mod p| i . i \<in> UNIV}"
        then obtain i where i:"y = a^i mod p" by auto
        def q \<equiv> "i div x" def r \<equiv> "i mod x"
        have "i = q*x + r" by (simp add: r_def q_def)
        hence y_q_r:"y = (((a ^ (q*x)) mod p) * ((a ^ r) mod p)) mod p"
          by (simp add: i power_add mod_mult_eq[symmetric])
        have "a ^ (q*x) mod p = (a ^ x mod p) ^ q mod p"
          by (simp add: power_mod mult.commute power_mult[symmetric])
        hence y_r:"y = a ^ r mod p" using `p\<ge>2` x by (simp add: cong_nat_def y_q_r)
        have "y \<in> {a ^ i mod p | i. 0 < i \<and> i \<le> x}"
        proof (cases)
          assume "r = 0"
            hence "y = a^x mod p" using `p\<ge>2` x by (simp add: cong_nat_def y_r)
            thus ?thesis using x by blast
          next
          assume "r \<noteq> 0"
            thus ?thesis using x by (auto simp add: y_r r_def)
        qed
      }
      thus " {a ^ i mod p|i. i \<in> UNIV} \<subseteq> {a ^ i mod p | i. 0 < i \<and> i \<le> x}" by auto
    qed
    note X = this

    have "p - 1 = card {1 .. p - 1}" by auto
    also have "{1 .. p - 1} = {a^i mod p | i. 1 \<le> i \<and> i \<le> x}" using X a by auto
    also have "\<dots> = (\<lambda> i. a^i mod p) ` {1..x}" by auto
    also have "card \<dots> \<le> p - 2"
      using Finite_Set.card_image_le[of "{1..x}" "\<lambda> i. a^i mod p"] x by auto
    finally have False using `2 \<le> p` by arith
   }
   hence "\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p)" by auto
 } note a_is_gen = this
 {
    assume "a>1"
    have "\<not> p dvd a "
    proof (rule ccontr)
      assume "\<not> \<not> p dvd a"
      hence "p dvd a" by auto
      have "p \<le> a" using dvd_nat_bounds[OF _ `p dvd a`] a by simp
      thus False using `a>1` a by force
    qed
    hence "coprime a p" using prime_imp_coprime_nat[OF prime_p]  by (simp add: gcd_commute_nat)
    hence "coprime (int a) (int p)" by (simp add: transfer_int_nat_gcd(1))
    have "phi (int p) = p - 1"
      by (metis nat_int phi_prime prime_p) 
    hence "[a^(p - 1) = 1] (mod p)" using euler_theorem[OF _ `coprime (int a) (int p)`]
      by (simp add: of_nat_power transfer_int_nat_cong[symmetric])
  }
  hence "[a^(p - 1) = 1] (mod p)" using a by fastforce
  thus ?thesis using a_is_gen a by auto
 qed

theorem converse_lehmer:
 assumes prime_p:"prime(p)"
 shows "\<exists> a . [a^(p - 1) = 1] (mod p) \<and>
              (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))
              \<and> a > 0 \<and> a < p"
 proof -
  have "p \<ge> 2" by (rule prime_ge_2_nat[OF prime_p])
  obtain a where a:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))
                    \<and> a > 0 \<and> a < p"
    using converse_lehmer_weak[OF prime_p] by blast
  { fix q assume q:"q \<in> prime_factors (p - 1)"
    hence "0 < q \<and> q \<le> p - 1" using `p\<ge>2` 
      by (auto simp add: dvd_nat_bounds prime_factors_dvd_nat prime_factors_gt_0_nat)
    hence "(p - 1) div q \<ge> 1" using div_le_mono[of "q" "p - 1" q] div_self[of q] by simp
    have "q \<ge> 2" using q by (simp add: prime_factors_prime_nat prime_ge_2_nat)
    hence "(p - 1) div q < p - 1" using `p \<ge> 2` by simp
    hence "[a^((p - 1) div q) \<noteq> 1] (mod p)" using a `(p - 1) div q \<ge> 1`
      by (auto simp add: Suc_diff_Suc less_eq_Suc_le)
  }
  thus ?thesis using a by auto
 qed

end
