subsection \<open>Gauss Formula\label{sec:card_irred}\<close>

theory Card_Irreducible_Polynomials
  imports
    Dirichlet_Series.Moebius_Mu
    Card_Irreducible_Polynomials_Aux
begin

hide_const "Polynomial.order"

text \<open>The following theorem is a slightly generalized form of the formula discovered by
Gauss for the number of monic irreducible polynomials over a finite field. He originally verified
the result for the case when @{term "R"} is a simple prime field.
The version of the formula here for the case where @{term "R"} may be an arbitrary finite field can
be found in Chebolu and Min{\'a}{\v{c}}~\<^cite>\<open>"chebolu2010"\<close>.\<close>

theorem (in finite_field) card_irred:
  assumes "n > 0"
  shows "n * card {f. monic_irreducible_poly R f \<and> degree f = n} =
    (\<Sum>d | d dvd n. moebius_mu d * (order R^(n div d)))"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = dirichlet_prod moebius_mu (\<lambda>x. int (order R) ^ x) n"
    using card_irred_aux
    by (intro moebius_inversion assms) (simp flip:of_nat_power)
  also have "... = ?rhs"
    by (simp add:dirichlet_prod_def)
  finally show ?thesis by simp
qed

text \<open>In the following an explicit analytic lower bound for the cardinality of monic irreducible
polynomials is shown, with which existence follows. This part deviates from the classic approach,
where existence is verified using a divisibility argument. The reason for the deviation is that an
analytic bound can also be used to estimate the runtime of a randomized algorithm selecting an
irreducible polynomial, by randomly sampling monic polynomials.\<close>

lemma (in finite_field) card_irred_1:
  "card {f. monic_irreducible_poly R f \<and> degree f = 1} = order R"
proof -
  have "int (1 * card {f. monic_irreducible_poly R f \<and> degree f = 1})
    = int (order R)"
    by (subst card_irred, auto)
  thus ?thesis by simp
qed

lemma (in finite_field) card_irred_2:
  "real (card {f. monic_irreducible_poly R f \<and> degree f = 2}) =
    (real (order R)^2 - order R) / 2"
proof -
  have "x dvd 2 \<Longrightarrow> x = 1 \<or> x = 2" for x :: nat
    using nat_dvd_not_less[where m="2"]
    by (metis One_nat_def even_zero gcd_nat.strict_trans2
        less_2_cases nat_neq_iff pos2)
  hence a: "{d. d dvd 2} = {1,2::nat}"
    by (auto simp add:set_eq_iff)

  have "2*real (card {f. monic_irreducible_poly R f \<and> degree f = 2})
    = of_int (2* card {f. monic_irreducible_poly R f \<and> degree f = 2})"
    by simp
  also have "... =
    of_int (\<Sum>d | d dvd 2. moebius_mu d * int (order R) ^ (2 div d))"
    by (subst card_irred, auto)
  also have "... = order R^2 - int (order R)"
    by (subst a, simp)
  also have "... = real (order R)^2 - order R"
    by simp
  finally have
    "2 * real (card {f. monic_irreducible_poly R f \<and> degree f = 2}) =
    real (order R)^2 - order R"
    by simp
  thus ?thesis by simp
qed

lemma (in finite_field) card_irred_gt_2:
  assumes "n > 2"
  shows "real (order R)^n / (2*real n) \<le>
    card {f. monic_irreducible_poly R f \<and> degree f = n}"
    (is "?lhs \<le> ?rhs")
proof -
  let ?m = "real (order R)"
  have a:"?m \<ge> 2"
    using finite_field_min_order by simp

  have b:"moebius_mu n \<ge> -(1::real)" for n :: nat
    using abs_moebius_mu_le[where n="n"]
    unfolding abs_le_iff by auto

  have c: "n > 0" using assms by simp
  have d: "x < n - 1" if d_assms: "x dvd n" "x \<noteq> n" for x :: nat
  proof -
    have "x < n"
      using d_assms dvd_nat_bounds c by auto
    moreover have "\<not>(n-1 dvd n)" using assms
      by (metis One_nat_def Suc_diff_Suc c diff_zero
          dvd_add_triv_right_iff nat_dvd_1_iff_1
          nat_neq_iff numeral_2_eq_2 plus_1_eq_Suc)
    hence "x \<noteq> n-1" using d_assms by auto
    ultimately show "x < n-1"  by simp
  qed

  have "?m^n / 2 = ?m^n - ?m^n/2" by simp
  also have "... \<le> ?m^n - ?m^n/?m^1"
    using a by (intro diff_mono divide_left_mono, simp_all)
  also have "... \<le> ?m^n - ?m^(n-1)"
    using a c by (subst power_diff, simp_all)
  also have "... \<le> ?m^n - (?m^(n-1) - 1)/1" by simp
  also have "... \<le> ?m^n - (?m^(n-1)-1)/(?m-1)"
    using a by (intro diff_left_mono divide_left_mono, simp_all)
  also have "... = ?m^n - (\<Sum>i \<in> {..<n-1}. ?m^i)"
    using a by (subst geometric_sum, simp_all)
  also have "... \<le> ?m^n - (\<Sum>i \<in> {k. k dvd n \<and> k \<noteq> n}. ?m^i)"
    using d
    by (intro diff_mono sum_mono2 subsetI, auto simp add:not_less)
  also have "... = ?m^n + (\<Sum>i \<in> {k. k dvd n \<and> k \<noteq> n}. (-1) * ?m^i)"
    by (subst sum_distrib_left[symmetric], simp)
  also have "... \<le> moebius_mu 1 * ?m^n +
    (\<Sum>i \<in> {k. k dvd n \<and> k \<noteq> n}. moebius_mu (n div i) * ?m^i)"
    using b
    by (intro add_mono sum_mono mult_right_mono)
      (simp_all add:not_less)
  also have "... =  (\<Sum>i \<in> insert n {k. k dvd n \<and> k \<noteq> n}.
    moebius_mu (n div i) * ?m^i)"
    using c by (subst sum.insert, auto)
  also have "... = (\<Sum>i \<in> {k. k dvd n}. moebius_mu (n div i) * ?m^i)"
    by (intro sum.cong, auto simp add:set_eq_iff)
  also have "... = dirichlet_prod (\<lambda>i. ?m^i) moebius_mu n"
    unfolding dirichlet_prod_def by (intro sum.cong, auto)
  also have "... = dirichlet_prod moebius_mu (\<lambda>i. ?m^i) n"
    using dirichlet_prod_commutes by metis
  also have "... =
    of_int (\<Sum>d | d dvd n. moebius_mu d * order R^(n div d))"
    unfolding dirichlet_prod_def by simp
  also have "... = of_int (n *
    card {f. monic_irreducible_poly R f \<and> length f - 1 = n})"
    using card_irred[OF c] by simp
  also have "... = n * ?rhs" by simp
  finally have "?m^n / 2 \<le> n * ?rhs" by simp
  hence "?m ^ n \<le> 2 * n * ?rhs" by simp
  hence "?m^n/(2*real n) \<le> ?rhs"
    using c by (subst pos_divide_le_eq, simp_all add:algebra_simps)
  thus ?thesis by simp
qed

lemma (in finite_field) exist_irred:
  assumes "n > 0"
  obtains f where "monic_irreducible_poly R f" "degree f = n"
proof -
  consider (i) "n = 1" | (ii) "n = 2" | (iii) "n>2"
    using assms by linarith
  then have
    "card {f. monic_irreducible_poly R f \<and> degree f = n} > 0"
    (is "card ?A > 0")
  proof (cases)
    case i
    hence "card ?A = order R"
      using card_irred_1 by simp
    also have "... > 0"
       using finite_field_min_order by simp
    finally show ?thesis by simp
  next
    case ii
    have "0 < (real (order R) * (real (order R) - 1)) / 2"
      using finite_field_min_order by simp
    also have "... = (real (order R)^2 - order R) / 2"
      by (simp add:power2_eq_square algebra_simps)
    also have "... = real (card ?A)"
      using ii by (subst card_irred_2[symmetric], simp)
    finally have " 0 < real (card ?A)" by simp
    then show ?thesis by simp
  next
    case iii
    have "0 < real (order R)^n / (2*real n)"
      using finite_field_min_order assms by simp
    also have "... \<le> real (card ?A)"
      using iii card_irred_gt_2 by simp
    finally have "0 < real (card ?A)" by simp
    then show ?thesis by simp
  qed
  hence "?A \<noteq> {}"
    by (metis card.empty nless_le)
  then obtain f where "monic_irreducible_poly R f" "degree f = n"
    by auto
  thus ?thesis using that by simp
qed

theorem existence:
  assumes "n > 0"
  assumes "Factorial_Ring.prime p"
  shows "\<exists>(F:: int set list set ring). finite_field F \<and> order F = p^n"
proof -
  interpret zf: finite_field "ZFact (int p)"
    using zfact_prime_is_finite_field assms by simp

  interpret zfp: polynomial_ring "ZFact p" "carrier (ZFact p)"
    unfolding polynomial_ring_def polynomial_ring_axioms_def
    using zf.field_axioms zf.carrier_is_subfield by simp

  have p_gt_0: "p > 0" using prime_gt_0_nat assms(2) by simp

  obtain f where f_def:
    "monic_irreducible_poly (ZFact (int p)) f"
    "degree f = n"
    using zf.exist_irred assms by auto

  let ?F  = "Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f"
  have "f \<in> carrier (poly_ring (ZFact (int p)))"
    using f_def(1) zf.monic_poly_carr
    unfolding monic_irreducible_poly_def
    by simp
  moreover have "degree f > 0"
    using assms(1) f_def by simp
  ultimately have "order ?F =  card (carrier (ZFact p))^degree f"
    by (intro zf.rupture_order[OF zf.carrier_is_subfield]) auto
  hence a:"order ?F = p^n"
    unfolding f_def(2) card_zfact_carr[OF p_gt_0] by simp

  have "field ?F"
    using f_def(1) zf.monic_poly_carr monic_irreducible_poly_def
    by (subst zfp.rupture_is_field_iff_pirreducible) auto
  moreover have "order ?F > 0"
    unfolding a using assms(1,2) p_gt_0 by simp
  ultimately have b:"finite_field ?F"
    using card_ge_0_finite
    by (intro finite_fieldI, auto simp add:Coset.order_def)

  show ?thesis
    using a b
    by (intro exI[where x="?F"], simp)
qed

end
