section \<open>Primitive roots in an integral domain\<close>
theory Primitive_Roots
imports 
  Complex_Main 
  "HOL-Number_Theory.Cong"
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Library.Real_Mod"
begin

text \<open>
  We define the notion of a primitive root in an integral domain: an $n$-th root of unity
  that is not a $k$-th root of unity for any $k < n$ and therefore generates all $n$-th roots
  of unity.
\<close>

locale primroot =
  fixes n :: nat and w :: "'a :: idom"
  assumes pos_order: "n > 0"
  assumes root_of_unity: "w ^ n = 1"
  assumes primitive: "\<And>k. 0 < k \<Longrightarrow> k < n \<Longrightarrow> w ^ k \<noteq> 1"
begin

lemma nonzero: "w \<noteq> 0"
  using root_of_unity pos_order by (auto simp: power_0_left)

lemma power_eq_iff: "w ^ k = w ^ l \<longleftrightarrow> [k = l] (mod n)"
proof (induction k l rule: linorder_wlog)
  case (le k l)
  define m where "m = l - k"
  have l: "l = k + m"
    using le by (simp add: m_def)

  define a where "a = m div n"
  define b where "b = m mod n"
  have m: "m = n * a + b"
    by (simp add: a_def b_def)
  have b: " b < n"
    using pos_order by (simp add: b_def)

  have "w ^ k = w ^ l \<longleftrightarrow> w ^ k = w ^ k * w ^ m"
    by (simp add: l power_add)
  also have "\<dots> \<longleftrightarrow> w ^ m = 1"
    using nonzero by simp
  also have "\<dots> \<longleftrightarrow> w ^ b = 1"
    by (simp add: m power_add power_mult root_of_unity)
  also have "\<dots> \<longleftrightarrow> b = 0"
    using primitive[of b] b by (cases "b = 0") auto
  also have "\<dots> \<longleftrightarrow> [k = l] (mod n)"
    by (simp add: l cong_altdef_nat' b_def mod_eq_0_iff_dvd)
  finally show ?case .
qed (simp add: cong_sym_eq eq_commute)

lemma inj_on_power: "inj_on (\<lambda>k. w ^ k) {..<n}"
  by (auto intro!: inj_onI simp: power_eq_iff cong_def)

end


locale primroot_field = primroot n w for n and w :: "'a :: field"
begin

lemma power_int_eq_iff: "w powi k = w powi l \<longleftrightarrow> [k = l] (mod (int n))"
proof -
  define a where "a = min k l"
  define k' where "k' = nat (k - a)"
  define l' where "l' = nat (l - a)"
  have k: "k = a + int k'" and l: "l = a + int l'"
    by (simp_all add: k'_def l'_def a_def)
  have "w powi k = w powi l \<longleftrightarrow> [k' = l'] (mod n)"
    using nonzero by (simp add: k l power_int_add power_eq_iff)
  also have "\<dots> \<longleftrightarrow> [k = l] (mod (int n))"
    by (simp add: k l cong_add_lcancel cong_int_iff)
  finally show ?thesis .
qed

end


interpretation primroot_1: primroot 1 1
  by standard auto

interpretation primroot_neg1: primroot 2 "-1 :: 'a :: {idom, ring_char_0}"
  by standard (auto simp: numeral_2_eq_2 less_Suc_eq)

locale primroot_cis =
  fixes n :: nat and k :: int
  assumes coprime: "coprime k n"
  assumes pos_order': "n > 0"
begin

sublocale primroot n "cis (2 * pi * k / n)"
proof
  show "n > 0"
    using pos_order' by simp
next
  show "cis (2 * pi * real_of_int k / real n) ^ n = 1"
    using pos_order' by (simp add: Complex.DeMoivre)
next
  fix j :: nat assume j: "j > 0" "j < n"
  show "cis (2 * pi * real_of_int k / real n) ^ j \<noteq> 1"
  proof
    assume "cis (2 * pi * real_of_int k / real n) ^ j = 1"
    then obtain l where "real j * (2 * pi * real_of_int k / real n) = real_of_int l * (2 * pi)"
      unfolding Complex.DeMoivre cis_eq_1_iff by blast
    hence "real_of_int (k * j) = real_of_int (l * n)"
      unfolding of_int_mult using pos_order' by (simp add: field_simps)
    hence eq: "k * j = l * n"
      by linarith
    have "n dvd k * j"
      by (simp add: eq)
    with coprime have "n dvd j"
      by (simp add: coprime_commute coprime_dvd_mult_right_iff)
    with j show False
      by force
  qed
qed

end

interpretation primroot_ii: primroot 4 \<i>
proof -
  interpret primroot_cis 4 1
    by standard auto
  show "primroot 4 \<i>"
    using primroot_axioms by simp
qed

lemma (in primroot) cyclotomic_poly_conv_prod_unity_root:
  "Polynomial.monom 1 n - 1 = (\<Prod>k<n. [:-(w ^ k), 1:])" (is "?lhs = ?rhs")
proof (rule ccontr)
  assume neq: "?lhs \<noteq> ?rhs"
  have "?lhs = Polynomial.monom 1 n + (-1)"
    by simp
  also have "degree \<dots> = n"
    by (subst degree_add_eq_left) (use pos_order in \<open>auto simp: degree_monom_eq\<close>)
  finally have deg1: "degree ?lhs = n" .

  have "poly.coeff (?lhs - ?rhs) n = 0"
  proof -
    have "poly.coeff ?rhs n = lead_coeff ?rhs"
      by (simp add: degree_prod_sum_eq)
    also have "\<dots> = 1"
      by (subst lead_coeff_prod) auto
    finally show ?thesis
      using pos_order by simp
  qed
  moreover have "?lhs - ?rhs \<noteq> 0"
    using neq by simp
  ultimately have "degree (?lhs - ?rhs) \<noteq> n"
    by (metis leading_coeff_0_iff)
  moreover have "degree (?lhs - ?rhs) \<le> n"
    by (rule degree_diff_le) (use deg1 in \<open>auto simp: degree_prod_sum_eq\<close>)
  ultimately have "degree (?lhs - ?rhs) < n"
    by linarith

  have root1: "poly ?lhs (w ^ k) = 0" for k
  proof -
    have "poly ?lhs (w ^ k) = w ^ (n * k) - 1"
      by (simp add: poly_monom mult_ac flip: power_mult)
    also have "\<dots> = 0"
      by (simp add: power_mult root_of_unity)
    finally show ?thesis .
  qed
  have root2: "poly ?rhs (w ^ k) = 0" if "k < n" for k
    using that by (auto simp: poly_prod)

  have "inj_on (\<lambda>k. w ^ k) {..<n}"
    by (rule inj_on_power)
  hence "card {..<n} = card ((\<lambda>k. w ^ k) ` {..<n})"
    by (subst card_image) auto
  also have "card ((\<lambda>k. w ^ k) ` {..<n}) \<le> card {z. poly (?lhs - ?rhs) z = 0}"
    by (intro card_mono poly_roots_finite) (use neq root1 root2 in auto)
  also have "card {z. poly (?lhs - ?rhs) z = 0} \<le> degree (?lhs - ?rhs)"
    by (rule poly_roots_degree) (use neq in auto)
  also have "\<dots> < n"
    by fact
  finally show False
    by simp
qed

lemma (in primroot) cyclotomic_poly_conv_prod_unity_root':
  "1 - Polynomial.monom 1 n = (\<Prod>k<n. [:1, -(w ^ k):])" (is "?lhs = ?rhs")
proof -
  define A where "A = insert 0 ((\<lambda>k. w ^ k) ` {..<n})"
  have card_A: "card A = Suc n"
  proof -
    have "card A = Suc (card ((\<lambda>k. w ^ k) ` {..<n}))"
      unfolding A_def using nonzero by (subst card.insert) auto
    also have "card ((\<lambda>k. w ^ k) ` {..<n}) = n"
      by (subst card_image) (use pos_order inj_on_power in auto)
    finally show ?thesis .
  qed

  show ?thesis
  proof (rule poly_eqI_degree)
    have "degree (1 - Polynomial.monom 1 n :: 'a poly) \<le> n"
      by (intro degree_diff_le) (auto simp: degree_monom_eq)
    thus "degree (1 - Polynomial.monom 1 n :: 'a poly) < card A"
      by (simp add: card_A)
  next
    have "degree (\<Prod>k<n. [:1, - (w ^ k):]) \<le> n"
      by (rule order.trans[OF degree_prod_sum_le]) (auto simp: nonzero)
    thus "degree (\<Prod>k<n. [:1, - (w ^ k):]) < card A"
      by (simp add: card_A)
  next
    fix x assume x: "x \<in> A"
    have "poly (1 - Polynomial.monom 1 n) (w ^ k) = 0" for k
    proof -
      have "poly (1 - Polynomial.monom 1 n) (w ^ k) = 1 - w ^ (n * k)"
        by (simp add: poly_monom mult_ac flip: power_mult)
      also have "\<dots> = 0"
        by (simp add: power_mult root_of_unity)
      finally show ?thesis .
    qed
    moreover have "poly (1 - Polynomial.monom 1 n :: 'a poly) 0 = 1"
      using pos_order by (simp add: poly_monom power_0_left)
    moreover have "poly (\<Prod>k<n. [:1, -(w ^ k):]) (w ^ k) = 0" if k: "k < n" for k
    proof -
      define k' where "k' = (if k = 0 then 0 else n - k)"
      have "k' < n"
        using pos_order k by (auto simp: k'_def)
      have "w ^ k * w ^ k' = w ^ (k + k')"
        by (simp add: power_add)
      also have "\<dots> = w ^ 0"
        by (subst power_eq_iff) (use k in \<open>auto simp: k'_def cong_def\<close>)
      finally show ?thesis
        using that \<open>k' < n\<close> by (auto simp: poly_prod)
    qed
    moreover have "poly (\<Prod>k<n. [:1, -(w ^ k):]) 0 = 1"
      by (simp add: poly_prod)
    ultimately show "poly (1 - Polynomial.monom 1 n) x = poly (\<Prod>k<n. [:1, -(w ^ k):]) x"
      using x by (auto simp: A_def)
  qed
qed

end