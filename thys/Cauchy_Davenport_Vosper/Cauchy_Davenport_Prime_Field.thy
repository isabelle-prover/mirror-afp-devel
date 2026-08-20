theory Cauchy_Davenport_Prime_Field
  imports
    Sumset_Basics
    "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

section \<open>Cauchy-Davenport over prime fields\<close>

text \<open>
  This theory proves the prime-field Cauchy-Davenport theorem by a
  polynomial-method argument. The core technical work packages the bivariate
  degree bookkeeping needed to show that a suitably chosen polynomial cannot
  vanish on too large a grid unless the expected lower bound holds.
\<close>

subsection \<open>Polynomial infrastructure\<close>

definition total_degree_le :: "'a::comm_semiring_1 poly poly \<Rightarrow> nat \<Rightarrow> bool" where
  "total_degree_le P d \<longleftrightarrow>
    (\<forall>i. if i \<le> d then degree (poly.coeff P i) \<le> d - i else poly.coeff P i = 0)"

definition sum_factor :: "'a::comm_ring_1 \<Rightarrow> 'a poly poly" where
  "sum_factor c = [: [:-c, 1:], [:1:] :]"

lemma coeff_poly_const:
  fixes P :: "'a::comm_semiring_1 poly poly"
  shows "poly.coeff (poly P [:a:]) j =
    (\<Sum>i\<le>degree P. poly.coeff (poly.coeff P i) j * a ^ i)"
proof -
  have "poly.coeff (poly P [:a:]) j =
      poly.coeff (\<Sum>i\<le>degree P. poly.coeff P i * [:a:] ^ i) j"
    by (simp add: poly_altdef)
  also have "\<dots> =
      (\<Sum>i\<le>degree P. poly.coeff (poly.coeff P i * [:a:] ^ i) j)"
    by (simp add: coeff_sum)
  also have "\<dots> =
      (\<Sum>i\<le>degree P. poly.coeff (poly.coeff P i) j * a ^ i)"
  proof (intro sum.cong refl)
    fix i
    assume "i \<in> {..degree P}"
    have "[:a:] ^ i = [:a ^ i:]"
      by (induction i) (simp_all add: mult.commute)
    then show "poly.coeff (poly.coeff P i * [:a:] ^ i) j =
        poly.coeff (poly.coeff P i) j * a ^ i"
      by (simp add: coeff_mult mult.commute mult.left_commute mult.assoc)
  qed
  finally show ?thesis .
qed

lemma total_degree_le_eval_const:
  fixes P :: "'a::comm_semiring_1 poly poly"
  assumes td: "total_degree_le P d"
  shows "degree (poly P [:a:]) \<le> d"
proof -
  have zero_above: "poly.coeff (poly P [:a:]) j = 0" if j: "j > d" for j
  proof -
    have eval_coeff: "poly.coeff (poly P [:a:]) j =
        (\<Sum>i\<le>degree P. poly.coeff (poly.coeff P i) j * a ^ i)"
      by (rule coeff_poly_const)
    have sum_zero: "(\<Sum>i\<le>degree P. poly.coeff (poly.coeff P i) j * a ^ i) = 0"
    proof (intro sum.neutral ballI)
      fix i
      assume i: "i \<in> {..degree P}"
      show "poly.coeff (poly.coeff P i) j * a ^ i = 0"
      proof (cases "i \<le> d")
        case True
        with td have "degree (poly.coeff P i) \<le> d - i"
          by (simp add: total_degree_le_def)
        moreover from True j have "d - i < j"
          by simp
        ultimately have "poly.coeff (poly.coeff P i) j = 0"
          by (meson coeff_eq_0 le_less_trans)
        then show ?thesis
          by simp
      next
        case False
        with td have "poly.coeff P i = 0"
          by (simp add: total_degree_le_def)
        then show ?thesis
          by simp
      qed
    qed
    show ?thesis
      using eval_coeff sum_zero by simp
  qed
  show ?thesis
    by (rule degree_le) (use zero_above in blast)
qed

lemma total_degree_le_eval_const_top:
  fixes P :: "'a::comm_semiring_1 poly poly"
  assumes td: "total_degree_le P d"
  shows "poly.coeff (poly P [:a:]) d = poly.coeff (poly.coeff P 0) d"
proof -
  have "poly.coeff (poly P [:a:]) d =
      (\<Sum>i\<le>degree P. poly.coeff (poly.coeff P i) d * a ^ i)"
    by (rule coeff_poly_const)
  also have "\<dots> =
      poly.coeff (poly.coeff P 0) d * a ^ 0 +
      (\<Sum>i\<in>{..degree P} - {0}. poly.coeff (poly.coeff P i) d * a ^ i)"
    by (subst sum.remove[of "{..degree P}" 0 "\<lambda>i. poly.coeff (poly.coeff P i) d * a ^ i"]) simp_all
  also have "\<dots> = poly.coeff (poly.coeff P 0) d * a ^ 0"
  proof -
    have "(\<Sum>i\<in>{..degree P} - {0}. poly.coeff (poly.coeff P i) d * a ^ i) = 0"
    proof (intro sum.neutral ballI)
      fix i
      assume i: "i \<in> {..degree P} - {0}"
      then have i_pos: "0 < i"
        by simp
      show "poly.coeff (poly.coeff P i) d * a ^ i = 0"
      proof (cases "i \<le> d")
        case True
        with td have deg_i: "degree (poly.coeff P i) \<le> d - i"
        by (simp add: total_degree_le_def)
      from True i_pos have "d - i < d"
        by simp
      with deg_i have "poly.coeff (poly.coeff P i) d = 0"
        by (meson coeff_eq_0 le_less_trans)
        then show ?thesis
          by simp
      next
        case False
        with td have "poly.coeff P i = 0"
          by (simp add: total_degree_le_def)
        then show ?thesis
          by simp
      qed
    qed
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    by simp
qed

lemma coeff_sum_factor_mult_0:
  "poly.coeff (sum_factor c * P) 0 = [:-c, 1:] * poly.coeff P 0"
  by (simp add: sum_factor_def coeff_mult)

lemma coeff_sum_factor_mult_Suc:
  "poly.coeff (sum_factor c * P) (Suc i) =
    [:-c, 1:] * poly.coeff P (Suc i) + poly.coeff P i"
  by (simp add: sum_factor_def coeff_mult)

lemma total_degree_le_sum_factor_mult:
  fixes P :: "'a::field poly poly"
  assumes td: "total_degree_le P d"
  shows "total_degree_le (sum_factor c * P) (Suc d)"
unfolding total_degree_le_def
proof
  fix i
  show "(if i \<le> Suc d then degree (poly.coeff (sum_factor c * P) i) \<le> Suc d - i
         else poly.coeff (sum_factor c * P) i = 0)"
  proof (cases i)
    case 0
    have "degree (poly.coeff (sum_factor c * P) 0) =
        degree ([:-c, 1:] * poly.coeff P 0)"
      by (simp add: coeff_sum_factor_mult_0)
    also have "\<dots> \<le> degree [:-c, 1:] + degree (poly.coeff P 0)"
      by (rule degree_mult_le)
    also have "\<dots> \<le> Suc d"
    proof -
      have "degree (poly.coeff P 0) \<le> d"
      proof -
        from td have "if 0 \<le> d then degree (poly.coeff P 0) \<le> d - 0 else poly.coeff P 0 = 0"
          unfolding total_degree_le_def by blast
        then show ?thesis
          by simp
      qed
      then show ?thesis
        by simp
    qed
    finally show ?thesis
      using 0 by simp
  next
    case (Suc k)
    show ?thesis
    proof (cases "k \<le> d")
      case True
      have deg_Suc: "degree (poly.coeff P (Suc k)) \<le> d - Suc k"
      proof (cases "Suc k \<le> d")
        case True
        with td show ?thesis
          by (simp add: total_degree_le_def)
      next
        case False
        with td have "poly.coeff P (Suc k) = 0"
          by (simp add: total_degree_le_def)
        then show ?thesis
          by simp
      qed
      from True td have deg_k: "degree (poly.coeff P k) \<le> d - k"
        by (simp add: total_degree_le_def)
      have "degree (poly.coeff (sum_factor c * P) (Suc k)) =
          degree ([:-c, 1:] * poly.coeff P (Suc k) + poly.coeff P k)"
        by (simp add: coeff_sum_factor_mult_Suc)
      also have "\<dots> \<le>
          max (degree ([:-c, 1:] * poly.coeff P (Suc k))) (degree (poly.coeff P k))"
        by (rule degree_add_le_max)
      also have "\<dots> \<le> d - k"
      proof -
        have deg_lin: "degree ([:-c, 1:] * poly.coeff P (Suc k)) \<le> d - k"
        proof -
          show ?thesis
          proof (cases "poly.coeff P (Suc k) = 0")
            case True
            then show ?thesis
              by simp
          next
            case False
            have suc_le: "Suc k \<le> d"
            proof (rule ccontr)
              assume "\<not> Suc k \<le> d"
              with td have "poly.coeff P (Suc k) = 0"
                by (simp add: total_degree_le_def)
              with False show False
                by contradiction
            qed
            have "degree ([:-c, 1:] * poly.coeff P (Suc k)) =
                degree [:-c, 1:] + degree (poly.coeff P (Suc k))"
              by (rule degree_mult_eq) (use False in simp_all)
            also have "\<dots> \<le> 1 + (d - Suc k)"
              using deg_Suc by simp
            also have "\<dots> = d - k"
              using suc_le by simp
            finally show ?thesis .
          qed
        qed
        show ?thesis
          using deg_lin deg_k by simp
      qed
      finally show ?thesis
        using Suc True by simp
    next
      case False
      with td have zero_k: "poly.coeff P k = 0"
        by (simp add: total_degree_le_def)
      from False have "d < k"
        by simp
      then have "d < Suc k"
        by simp
      with td have zero_Suc: "poly.coeff P (Suc k) = 0"
        by (simp add: total_degree_le_def)
      show ?thesis
        using Suc zero_k zero_Suc by (simp add: coeff_sum_factor_mult_Suc)
    qed
  qed
qed

lemma total_degree_le_prod_sum_factor:
  fixes C :: "'a::field set"
  assumes "finite C"
  shows "total_degree_le (prod sum_factor C) (card C)"
  using assms
proof (induction rule: finite_induct)
  case empty
  show ?case
    by (simp add: total_degree_le_def)
next
  case (insert c C)
  then show ?case
    by (simp add: total_degree_le_sum_factor_mult)
qed

lemma coeff_coeff_sum_factor_mult_top:
  fixes P :: "'a::field poly poly"
  assumes td: "total_degree_le P d"
  assumes ij: "i + j = Suc d"
  shows "poly.coeff (poly.coeff (sum_factor c * P) i) j =
    (if i = 0 then 0 else poly.coeff (poly.coeff P (i - 1)) j) +
    (if j = 0 then 0 else poly.coeff (poly.coeff P i) (j - 1))"
proof (cases i)
  case 0
  with ij have j: "j = Suc d"
    by simp
  have "poly.coeff (poly.coeff (sum_factor c * P) 0) j =
      poly.coeff ([:-c, 1:] * poly.coeff P 0) j"
    by (simp add: coeff_sum_factor_mult_0)
  also have "\<dots> =
      poly.coeff (poly.coeff P 0) (j - 1) - c * poly.coeff (poly.coeff P 0) j"
    using j by (cases j) (simp_all add: coeff_mult)
  also have "poly.coeff (poly.coeff P 0) j = 0"
  proof -
    have "degree (poly.coeff P 0) \<le> d"
    proof -
      have "if 0 \<le> d then degree (poly.coeff P 0) \<le> d - 0 else poly.coeff P 0 = 0"
        using td unfolding total_degree_le_def by blast
      then show ?thesis
        by simp
    qed
    with j show ?thesis
      by (meson coeff_eq_0 less_Suc_eq_le)
  qed
  finally show ?thesis
    using 0 j by simp
next
  case (Suc k)
  have rec: "poly.coeff (poly.coeff (sum_factor c * P) (Suc k)) j =
      (if j = 0 then 0 else poly.coeff (poly.coeff P (Suc k)) (j - 1)) -
      c * poly.coeff (poly.coeff P (Suc k)) j +
      poly.coeff (poly.coeff P k) j"
  proof -
    have "poly.coeff (poly.coeff (sum_factor c * P) (Suc k)) j =
        poly.coeff ([:-c, 1:] * poly.coeff P (Suc k) + poly.coeff P k) j"
      by (simp add: coeff_sum_factor_mult_Suc)
    also have "\<dots> =
        poly.coeff ([:-c, 1:] * poly.coeff P (Suc k)) j +
        poly.coeff (poly.coeff P k) j"
      by simp
    also have "poly.coeff ([:-c, 1:] * poly.coeff P (Suc k)) j =
        (if j = 0 then 0 else poly.coeff (poly.coeff P (Suc k)) (j - 1)) -
        c * poly.coeff (poly.coeff P (Suc k)) j"
    proof (cases j)
      case 0
      then show ?thesis
        by (simp add: coeff_mult)
    next
      case (Suc l)
      then show ?thesis
        by (simp add: coeff_mult)
    qed
    finally show ?thesis
      by simp
  qed
  have zero_term: "poly.coeff (poly.coeff P (Suc k)) j = 0"
  proof (cases "Suc k \<le> d")
    case True
    with td have "degree (poly.coeff P (Suc k)) \<le> d - Suc k"
      by (simp add: total_degree_le_def)
    moreover have "d - Suc k < j"
    proof -
      from ij Suc have "j = Suc d - Suc k"
        by simp
      with True show ?thesis
        by simp
    qed
    ultimately show ?thesis
      by (meson coeff_eq_0 le_less_trans)
  next
    case False
    with td show ?thesis
      by (simp add: total_degree_le_def)
  qed
  show ?thesis
    using Suc rec zero_term by (cases j) simp_all
qed

lemma coeff_coeff_prod_sum_factor_top:
  fixes C :: "'a::field set"
  assumes fin: "finite C"
  assumes ij: "i + j = card C"
  shows "poly.coeff (poly.coeff (prod sum_factor C) i) j = of_nat (card C choose i)"
  using fin ij
proof (induction C arbitrary: i j rule: finite_induct)
  case empty
  then have "i = 0" "j = 0"
    by simp_all
  then show ?case
    by simp
next
  case (insert c C)
  let ?P = "prod sum_factor C"
  have td: "total_degree_le ?P (card C)"
    using insert.hyps by (simp add: total_degree_le_prod_sum_factor)
  have ij': "i + j = Suc (card C)"
    using insert.prems insert.hyps by simp
  have top_rec:
    "poly.coeff (poly.coeff (prod sum_factor (insert c C)) i) j =
      (if i = 0 then 0 else poly.coeff (poly.coeff ?P (i - 1)) j) +
      (if j = 0 then 0 else poly.coeff (poly.coeff ?P i) (j - 1))"
  proof -
    have "poly.coeff (poly.coeff (prod sum_factor (insert c C)) i) j =
        poly.coeff (poly.coeff (sum_factor c * ?P) i) j"
      using insert.hyps by simp
    also have "\<dots> =
        (if i = 0 then 0 else poly.coeff (poly.coeff ?P (i - 1)) j) +
        (if j = 0 then 0 else poly.coeff (poly.coeff ?P i) (j - 1))"
      using coeff_coeff_sum_factor_mult_top[OF td ij'] .
    finally show ?thesis .
  qed
  show ?case
  proof (cases "i = 0 \<or> j = 0")
    case True
    then show ?thesis
    proof
      assume "i = 0"
      with ij' have j: "j = Suc (card C)"
        by simp
      have "poly.coeff (poly.coeff (prod sum_factor (insert c C)) i) j =
          poly.coeff (poly.coeff ?P 0) (card C)"
        using top_rec \<open>i = 0\<close> j by simp
      also have "\<dots> = of_nat (card C choose 0)"
        using insert.IH[of 0 "card C"] by simp
      finally show ?thesis
        using \<open>i = 0\<close> by simp
    next
      assume "j = 0"
      with ij' have i: "i = Suc (card C)"
        by simp
      have "poly.coeff (poly.coeff (prod sum_factor (insert c C)) i) j =
          poly.coeff (poly.coeff ?P (card C)) 0"
        using top_rec \<open>j = 0\<close> i by simp
      also have "\<dots> = of_nat (card C choose card C)"
        using insert.IH[of "card C" 0] by simp
      finally show ?thesis
        using i \<open>j = 0\<close> insert.hyps by simp
    qed
  next
    case False
    then have i_pos: "i > 0" and j_pos: "j > 0"
      by auto
    have split1: "i - 1 + j = card C" and split2: "i + (j - 1) = card C"
      using ij' i_pos j_pos by simp_all
    have "poly.coeff (poly.coeff (prod sum_factor (insert c C)) i) j =
        poly.coeff (poly.coeff ?P (i - 1)) j +
        poly.coeff (poly.coeff ?P i) (j - 1)"
      using top_rec False by simp
    also have "\<dots> = of_nat (card C choose (i - 1)) + of_nat (card C choose i)"
      using insert.IH[of "i - 1" j] insert.IH[of i "j - 1"] split1 split2 by simp
    also have "\<dots> = of_nat (Suc (card C) choose i)"
      using i_pos by (cases i) simp_all
    finally show ?thesis
      using insert.hyps by simp
  qed
qed

lemma poly_sum_factor:
  "poly (poly (sum_factor c) [:x:]) y = x + y - c"
  by (simp add: sum_factor_def)

lemma prime_not_dvd_binomial:
  assumes "prime p" "k \<le> n" "n < p"
  shows "\<not> p dvd (n choose k)"
proof
  assume dvd_choose: "p dvd (n choose k)"
  have fact_expand: "fact n = fact k * fact (n - k) * (n choose k)"
    using binomial_fact_lemma[OF assms(2)] by (simp add: mult_ac)
  have "p dvd fact n"
    using dvd_choose fact_expand by simp
  with assms show False
    by (simp add: prime_dvd_fact_iff)
qed

lemma finite_subset_with_card:
  assumes "finite U" "n \<le> card U"
  shows "\<exists>V. V \<subseteq> U \<and> card V = n"
  using assms
proof (induction U arbitrary: n rule: finite_induct)
  case empty
  then show ?case
    by auto
next
  case (insert x U)
  show ?case
  proof (cases "n \<le> card U")
    case True
    then obtain V where "V \<subseteq> U" "card V = n"
      using insert.IH by blast
    then show ?thesis
      using insert.hyps by auto
  next
    case False
    have n_le: "n \<le> Suc (card U)"
      using insert.prems insert.hyps by simp
    from False have "Suc (card U) \<le> n"
      by simp
    with n_le have "n = Suc (card U)"
      by simp
    then show ?thesis
      using insert.hyps by auto
  qed
qed

lemma prime_card_eq_char:
  assumes prime_card: "prime (card (UNIV :: 'a::finite_field set))"
  shows "CHAR('a) = card (UNIV :: 'a set)"
proof -
  have "CHAR('a) dvd card (UNIV :: 'a set)"
    by (rule CHAR_dvd_CARD)
  moreover from prime_card have "\<And>m. m dvd card (UNIV :: 'a set) \<Longrightarrow> m = 1 \<or> m = card (UNIV :: 'a set)"
    by (simp add: prime_nat_iff)
  ultimately have "CHAR('a) = 1 \<or> CHAR('a) = card (UNIV :: 'a set)"
    by blast
  with CHAR_prime show ?thesis
    by auto
qed

lemma of_nat_binomial_ne_zero:
  assumes prime_card: "prime (card (UNIV :: 'a::finite_field set))"
  assumes "k \<le> n" "n < card (UNIV :: 'a set)"
  shows "of_nat (n choose k) \<noteq> (0 :: 'a)"
proof -
  have char_eq: "CHAR('a) = card (UNIV :: 'a set)"
    by (rule prime_card_eq_char[OF prime_card])
  have "\<not> CHAR('a) dvd (n choose k)"
    using assms by (simp add: char_eq prime_not_dvd_binomial prime_card_eq_char)
  then show ?thesis
    using of_nat_eq_0_iff_char_dvd by blast
qed

lemma coeff_x_factor_plus_const_0:
  "poly.coeff ([:-[:a:], 1:] * Q + [:R:]) 0 = - [:a:] * poly.coeff Q 0 + R"
  by (simp add: coeff_mult)

lemma coeff_x_factor_plus_const_Suc:
  "poly.coeff ([:-[:a:], 1:] * Q + [:R:]) (Suc i) =
    - [:a:] * poly.coeff Q (Suc i) + poly.coeff Q i"
  by (simp add: coeff_mult)

lemma total_degree_le_factor_out:
  fixes P Q :: "'a::field poly poly"
  assumes td: "total_degree_le P (Suc d)"
  assumes decomp: "P = [:-[:a:], 1:] * Q + [:R:]"
  shows "total_degree_le Q d"
proof -
  have outer_zero: "poly.coeff Q i = 0" if "d < i" for i
  proof (rule ccontr)
    assume nz: "poly.coeff Q i \<noteq> 0"
    let ?I = "{k. poly.coeff Q k \<noteq> 0}"
    have finI: "finite ?I"
    proof (rule finite_subset[of _ "{..degree Q}"])
      show "?I \<subseteq> {..degree Q}"
      proof
        fix k
        assume k_in: "k \<in> ?I"
        have nz_k: "poly.coeff Q k \<noteq> 0"
          using k_in by simp
        show "k \<in> {..degree Q}"
        proof (rule ccontr)
          assume "k \<notin> {..degree Q}"
          then have "degree Q < k"
            by simp
          then have "poly.coeff Q k = 0"
            by (rule coeff_eq_0)
          with nz_k show False
            by contradiction
        qed
      qed
    qed simp
    have i_in: "i \<in> ?I"
      using nz by simp
    let ?k = "Max ?I"
    have k_in: "?k \<in> ?I"
      by (rule Max_in[OF finI]) (use i_in in auto)
    have i_le_k: "i \<le> ?k"
      using finI i_in by (intro Max_ge) auto
    have q_suc_zero: "poly.coeff Q (Suc ?k) = 0"
    proof (rule ccontr)
      assume nz_suc: "poly.coeff Q (Suc ?k) \<noteq> 0"
      then have suc_in: "Suc ?k \<in> ?I"
        by simp
      have "Suc ?k \<le> ?k"
        using finI suc_in by (intro Max_ge) auto
      then show False
        by simp
    qed
    have "poly.coeff P (Suc ?k) = poly.coeff Q ?k"
      using decomp q_suc_zero by (simp add: coeff_x_factor_plus_const_Suc)
    moreover have "poly.coeff P (Suc ?k) = 0"
      using td that i_le_k by (simp add: total_degree_le_def)
    ultimately show False
      using k_in by simp
  qed
  have degree_bound: "degree (poly.coeff Q i) \<le> d - i" if "i \<le> d" for i
  proof (rule ccontr)
    assume bad: "\<not> degree (poly.coeff Q i) \<le> d - i"
    let ?I = "{k. k \<le> d \<and> degree (poly.coeff Q k) > d - k}"
    have finI: "finite ?I"
      by simp
    have i_in: "i \<in> ?I"
      using that bad by simp
    let ?k = "Max ?I"
    have k_in: "?k \<in> ?I"
      by (rule Max_in[OF finI]) (use i_in in auto)
    have k_le_d: "?k \<le> d" and deg_k: "degree (poly.coeff Q ?k) > d - ?k"
      using k_in by auto
    have next_bound: "degree (poly.coeff Q (Suc ?k)) \<le> d - Suc ?k"
    proof (cases "Suc ?k \<le> d")
      case True
      have "Suc ?k \<notin> ?I"
      proof
        assume suc_in: "Suc ?k \<in> ?I"
        have "Suc ?k \<le> ?k"
          using finI suc_in by (intro Max_ge) auto
        then show False
          by simp
      qed
      then show ?thesis
        using True by simp
    next
      case False
      have "poly.coeff Q (Suc ?k) = 0"
        using outer_zero False by simp
      then show ?thesis
        by simp
    qed
    have deg_tail: "degree (- [:a:] * poly.coeff Q (Suc ?k)) < degree (poly.coeff Q ?k)"
      using next_bound deg_k by (auto intro: le_less_trans simp: degree_mult_le)
    have "poly.coeff P (Suc ?k) =
        poly.coeff Q ?k + (- [:a:] * poly.coeff Q (Suc ?k))"
      using decomp by (simp add: coeff_x_factor_plus_const_Suc algebra_simps)
    then have eq_p: "poly.coeff P (Suc ?k) =
        poly.coeff Q ?k + (- [:a:] * poly.coeff Q (Suc ?k))" .
    have deg_sum: "degree (poly.coeff Q ?k + (- [:a:] * poly.coeff Q (Suc ?k))) =
        degree (poly.coeff Q ?k)"
      by (rule degree_add_eq_left[OF deg_tail])
    have deg_p: "degree (poly.coeff P (Suc ?k)) = degree (poly.coeff Q ?k)"
      using eq_p deg_sum by simp
    have "degree (poly.coeff P (Suc ?k)) \<le> Suc d - Suc ?k"
    proof -
      have "Suc ?k \<le> Suc d"
        using k_le_d by simp
      from td have step:
        "if Suc ?k \<le> Suc d
         then degree (poly.coeff P (Suc ?k)) \<le> Suc d - Suc ?k
         else poly.coeff P (Suc ?k) = 0"
        unfolding total_degree_le_def by blast
      with \<open>Suc ?k \<le> Suc d\<close> show ?thesis
        by simp
    qed
    then show False
      using deg_k deg_p by simp
  qed
  show ?thesis
    by (simp add: total_degree_le_def degree_bound outer_zero)
qed

lemma coeff_coeff_x_factor_top:
  fixes Q :: "'a::field poly poly"
  assumes td: "total_degree_le Q d"
  assumes mn: "m + n = d"
  shows "poly.coeff (poly.coeff ([:-[:a:], 1:] * Q + [:R:]) (Suc m)) n =
    poly.coeff (poly.coeff Q m) n"
proof -
  have "poly.coeff (poly.coeff ([:-[:a:], 1:] * Q + [:R:]) (Suc m)) n =
      poly.coeff (poly.coeff Q m) n - a * poly.coeff (poly.coeff Q (Suc m)) n"
    by (simp add: coeff_x_factor_plus_const_Suc coeff_mult)
  moreover have "poly.coeff (poly.coeff Q (Suc m)) n = 0"
  proof -
    show ?thesis
    proof (cases "Suc m \<le> d")
      case True
      have deg_bound: "degree (poly.coeff Q (Suc m)) \<le> d - Suc m"
        using td True by (simp add: total_degree_le_def)
      have "d - Suc m < n"
      proof -
        from mn have "n = d - m"
          by simp
        with True show ?thesis
          by simp
      qed
      with deg_bound show ?thesis
        by (meson coeff_eq_0 le_less_trans)
    next
      case False
      with td show ?thesis
        by (simp add: total_degree_le_def)
    qed
  qed
  ultimately show ?thesis
    by simp
qed

lemma grid_nonzero_from_top_coeff:
  fixes P :: "'a::field poly poly"
  assumes cardA: "card A = Suc m"
  assumes cardB: "card B = Suc n"
  assumes td: "total_degree_le P (m + n)"
  assumes top: "poly.coeff (poly.coeff P m) n \<noteq> 0"
  shows "\<exists>a\<in>A. \<exists>b\<in>B. poly (poly P [:a:]) b \<noteq> 0"
  using cardA td top cardB
proof (induction m arbitrary: A P)
  case 0
  show ?case
  proof -
    from "0.prems"(1) have "\<exists>a. A = {a}"
      by (simp add: card_1_singleton_iff)
    then obtain a where A: "A = {a}"
      by blast
    note td0 = "0.prems"(2)
    note top0 = "0.prems"(3)
    define R where "R = poly P [:a:]"
    have coeff_R: "poly.coeff R (0 + n) = poly.coeff (poly.coeff P 0) (0 + n)"
      unfolding R_def by (rule total_degree_le_eval_const_top[OF td0])
    have coeff_R_nz: "poly.coeff R n \<noteq> 0"
      using coeff_R top0 by simp
    then have nz_R: "R \<noteq> 0"
      by auto
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have vanish_B: "\<forall>b\<in>B. poly R b = 0"
        using A by (simp add: R_def)
      have "B \<subseteq> {b. poly R b = 0}"
        using vanish_B by auto
      then have "card B \<le> card {b. poly R b = 0}"
        by (intro card_mono poly_roots_finite[OF nz_R]) auto
      also have "\<dots> \<le> degree R"
        by (rule poly_roots_degree[OF nz_R])
      finally have cardB_le_degR: "card B \<le> degree R" .
      have degR': "degree R \<le> 0 + n"
        unfolding R_def by (rule total_degree_le_eval_const[OF td0])
      have degR: "degree R \<le> n"
        using degR' by simp
      show False
        using cardB cardB_le_degR degR by linarith
    qed
  qed
next
  case (Suc m)
  have "0 < card A"
    using Suc.prems(1) by simp
  then have "A \<noteq> {}"
    by auto
  then obtain a where a_in: "a \<in> A"
    by auto
  show ?case
  proof (cases "\<exists>b\<in>B. poly (poly P [:a:]) b \<noteq> 0")
    case True
    then show ?thesis
      using a_in by blast
  next
    case False
    define R where "R = poly P [:a:]"
    have vanish_R: "poly R b = 0" if "b \<in> B" for b
      using False that by (simp add: R_def)
    have dvd: "[:-[:a:], 1:] dvd (P - [:R:])"
    proof -
      have eval0: "poly (P - [:poly P [:a:]:]) [:a:] = 0"
        by simp
      have dvd0: "[:-[:a:], 1:] dvd (P - [:poly P [:a:]:])"
        using eval0 by (rule iffD1[OF poly_eq_0_iff_dvd])
      show ?thesis
        using dvd0 R_def by simp
    qed
    then obtain Q where Q: "P = [:-[:a:], 1:] * Q + [:R:]"
      by (auto simp: dvd_def algebra_simps)
    let ?A' = "A - {a}"
    have cardA': "card ?A' = Suc m"
      using Suc.prems(1) a_in by (simp add: card_Diff_singleton_if)
    have tdQ: "total_degree_le Q (m + n)"
    proof -
      have tdP': "total_degree_le P (Suc (m + n))"
        using Suc.prems(2) by simp
      show ?thesis
        by (rule total_degree_le_factor_out[OF tdP' Q])
    qed
    have topQ: "poly.coeff (poly.coeff Q m) n \<noteq> 0"
    proof -
      have coeff_eq:
        "poly.coeff (poly.coeff P (Suc m)) n = poly.coeff (poly.coeff Q m) n"
      proof -
        have "poly.coeff (poly.coeff ([:-[:a:], 1:] * Q + [:R:]) (Suc m)) n =
            poly.coeff (poly.coeff Q m) n"
          by (rule coeff_coeff_x_factor_top[OF tdQ]) simp
        then show ?thesis
          by (simp add: Q)
      qed
      with Suc.prems(3) show ?thesis
        by simp
    qed
    obtain x b where xb: "x \<in> ?A'" "b \<in> B" "poly (poly Q [:x:]) b \<noteq> 0"
      using Suc.IH[OF cardA' tdQ topQ cardB] by blast
    have x_neq_a: "x \<noteq> a"
      using xb by simp
    have "poly (poly P [:x:]) b = (x - a) * poly (poly Q [:x:]) b + poly R b"
    proof -
      have "poly (poly P [:x:]) b =
          poly (poly ([:-[:a:], 1:] * Q + [:R:]) [:x:]) b"
        using Q by simp
      also have "\<dots> = poly (poly ([:-[:a:], 1:] * Q) [:x:]) b + poly R b"
        by simp
      also have "poly (poly ([:-[:a:], 1:] * Q) [:x:]) b =
          (x - a) * poly (poly Q [:x:]) b"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    also have "\<dots> = (x - a) * poly (poly Q [:x:]) b"
      using xb vanish_R by simp
    also have "\<dots> \<noteq> 0"
      using xb x_neq_a by simp
    finally have "poly (poly P [:x:]) b \<noteq> 0" .
    then show ?thesis
      using xb by blast
  qed
qed

lemma sumset_eq_UNIV_if_large:
  fixes A B :: "'a::finite_field set"
  assumes "card (UNIV :: 'a set) < card A + card B - 1"
  assumes "A \<noteq> {}" "B \<noteq> {}"
  shows "sumset A B = UNIV"
proof
  show "sumset A B \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> sumset A B"
  proof
    fix x :: 'a
    let ?T = "translate x ((uminus) ` B)"
    have card_negB: "card ((uminus) ` B) = card B"
      by (intro card_image inj_onI) auto
    have card_T: "card ?T = card B"
      by (simp add: card_negB card_translate_eq)
    have "card A + card ?T = card (A \<union> ?T) + card (A \<inter> ?T)"
      using card_Un_Int[of A ?T] by simp
    moreover have "card (A \<union> ?T) \<le> card (UNIV :: 'a set)"
      by (rule card_mono) auto
    ultimately have "card (A \<inter> ?T) > 0"
      using assms card_T by linarith
    then have "A \<inter> ?T \<noteq> {}"
      by auto
    then obtain a where a: "a \<in> A \<inter> ?T"
      by auto
    then obtain b where b: "b \<in> B" "a = x + (- b)"
      by (auto simp: translate_iff)
    have a_in: "a \<in> A"
      using a by simp
    have "x = a + b"
      using b by simp
    moreover have "a + b \<in> sumset A B"
      using a_in b(1) by (rule sumsetI)
    ultimately show "x \<in> sumset A B"
      by simp
  qed
qed

subsection \<open>The main lower bound\<close>

text \<open>
  The final statement is the abstract prime-field version of Cauchy-Davenport:
  for nonempty finite subsets of a field whose cardinality is prime, the sumset
  has size at least the expected truncated lower bound.
\<close>

theorem cauchy_davenport_prime_field:
  fixes A B :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes "A \<noteq> {}" "B \<noteq> {}"
  shows "card (sumset A B) \<ge> min (card (UNIV :: 'a set)) (card A + card B - 1)"
proof (cases "card (UNIV :: 'a set) < card A + card B - 1")
  case True
  have "sumset A B = UNIV"
  proof (rule sumset_eq_UNIV_if_large)
    show "card (UNIV :: 'a set) < card A + card B - 1"
      using True by assumption
    show "A \<noteq> {}"
      using assms(2) .
    show "B \<noteq> {}"
      using assms(3) .
  qed
  then show ?thesis
    by simp
next
  case False
  let ?m = "card A - 1"
  let ?n = "card B - 1"
  have cardA_pos: "0 < card A" and cardB_pos: "0 < card B"
    using assms(2,3) by auto
  have cardA: "card A = Suc ?m" and cardB: "card B = Suc ?n"
    using cardA_pos cardB_pos by simp_all
  have mn_lt: "?m + ?n < card (UNIV :: 'a set)"
  proof -
    have le_card: "card A + card B - 1 \<le> card (UNIV :: 'a set)"
      using False by simp
    have "Suc (?m + ?n) = card A + card B - 1"
      using cardA cardB by simp
    with le_card have "Suc (?m + ?n) \<le> card (UNIV :: 'a set)"
      by simp
    then show ?thesis
      by simp
  qed
  show ?thesis
  proof (rule ccontr)
    assume bad: "\<not> card (sumset A B) \<ge> min (card (UNIV :: 'a set)) (card A + card B - 1)"
    have sumset_small: "card (sumset A B) \<le> ?m + ?n"
      using False bad assms by simp
    obtain C where C: "sumset A B \<subseteq> C" "C \<subseteq> UNIV" "card C = ?m + ?n"
      using exists_subset_between[of "sumset A B" "?m + ?n" UNIV] sumset_small mn_lt by auto
    define F where "F = prod sum_factor C"
    have tdF: "total_degree_le F (?m + ?n)"
    proof -
      have finC: "finite C"
        using C by auto
      have "total_degree_le F (card C)"
        unfolding F_def by (rule total_degree_le_prod_sum_factor[OF finC])
      with C show ?thesis
        by simp
    qed
    have topF: "poly.coeff (poly.coeff F ?m) ?n = of_nat ((?m + ?n) choose ?m)"
    proof -
      have finC: "finite C"
        using C by auto
      have mn_card: "?m + ?n = card C"
        using C by simp
      have "poly.coeff (poly.coeff F ?m) ?n = of_nat (card C choose ?m)"
        unfolding F_def by (rule coeff_coeff_prod_sum_factor_top[OF finC mn_card])
      with C show ?thesis
        by simp
    qed
    have topF_nz: "poly.coeff (poly.coeff F ?m) ?n \<noteq> 0"
      using of_nat_binomial_ne_zero[OF prime_card, of ?m "?m + ?n"] topF mn_lt by simp
    obtain a b where ab: "a \<in> A" "b \<in> B" "poly (poly F [:a:]) b \<noteq> 0"
      using grid_nonzero_from_top_coeff[OF cardA cardB tdF topF_nz] by blast
    have ab_sum: "a + b \<in> sumset A B"
      using ab(1,2) by (rule sumsetI)
    have "a + b \<in> C"
      using ab_sum C(1) by auto
    then have "poly (poly F [:a:]) b = 0"
    proof -
      have finC: "finite C"
        using C by auto
      have "poly (poly F [:a:]) b = (\<Prod>c\<in>C. (a + b - c))"
        using finC by (simp add: F_def poly_prod poly_sum_factor)
      also have "\<dots> = 0"
        using finC \<open>a + b \<in> C\<close> by (simp add: prod_zero)
      finally show ?thesis .
    qed
    with ab show False
      by simp
  qed
qed

end
