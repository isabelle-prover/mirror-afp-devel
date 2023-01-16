section \<open>Counting Irreducible Polynomials \label{sec:card_irred}\<close>

subsection \<open>The polynomial $X^n - X$\<close>

theory Card_Irreducible_Polynomials_Aux
imports
  "HOL-Algebra.Multiplicative_Group"
  Formal_Polynomial_Derivatives
  Monic_Polynomial_Factorization
begin

lemma (in domain)
  assumes "subfield K R"
  assumes "f \<in> carrier (K[X])" "degree f > 0"
  shows embed_inj: "inj_on (rupture_surj K f \<circ> poly_of_const) K"
    and rupture_order: "order (Rupt K f) = card K^degree f"
    and rupture_char: "char (Rupt K f) = char R"
proof -
  interpret p: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] by simp

  interpret I: ideal "PIdl\<^bsub>K[X]\<^esub> f" "K[X]"
    using p.cgenideal_ideal[OF assms(2)] by simp

  interpret d: ring "Rupt K f"
    unfolding rupture_def using I.quotient_is_ring by simp

  have e: "subring K R"
    using assms(1) subfieldE(1) by auto

  interpret h:
    ring_hom_ring "R \<lparr> carrier := K \<rparr>"
      "Rupt K f" "rupture_surj K f \<circ> poly_of_const"
    using rupture_surj_norm_is_hom[OF e assms(2)]
    using ring_hom_ringI2 subring_is_ring d.ring_axioms e
    by blast

  have "field (R \<lparr>carrier := K\<rparr>)"
    using assms(1) subfield_iff(2) by simp
  hence "subfield K (R\<lparr>carrier := K\<rparr>)"
    using ring.subfield_iff[OF subring_is_ring[OF e]] by simp
  hence b: "subfield (rupture_surj K f ` poly_of_const ` K) (Rupt K f)"
    unfolding image_image comp_def[symmetric]
    by (intro h.img_is_subfield rupture_one_not_zero assms, simp)

  have "inj_on poly_of_const K"
    using poly_of_const_inj inj_on_subset by auto
  moreover have
    "poly_of_const ` K \<subseteq> ((\<lambda>q. q pmod f) ` carrier (K [X]))"
  proof (rule image_subsetI)
    fix x assume "x \<in> K"
    hence f:
      "poly_of_const x \<in> carrier (K[X])"
      "degree (poly_of_const x) = 0"
      using poly_of_const_over_subfield[OF assms(1)] by auto
    moreover
    have "degree (poly_of_const x) < degree f"
      using f(2) assms by simp
    hence "poly_of_const x pmod f = poly_of_const x"
      by (intro pmod_const(2)[OF assms(1)] f assms(2), simp)
    ultimately show
      "poly_of_const x \<in> ((\<lambda>q. q pmod f) ` carrier (K [X]))"
      by force
  qed
  hence "inj_on (rupture_surj K f) (poly_of_const ` K)"
    using rupture_surj_inj_on[OF assms(1,2)] inj_on_subset by blast
  ultimately show d: "inj_on (rupture_surj K f \<circ> poly_of_const) K"
    using comp_inj_on by auto

  have a: "d.dimension (degree f) (rupture_surj K f ` poly_of_const ` K)
    (carrier (Rupt K f))"
    using rupture_dimension[OF assms(1-3)] by auto
  then obtain base where base_def:
    "set base \<subseteq> carrier (Rupt K f)"
    "d.independent (rupture_surj K f ` poly_of_const ` K) base"
    "length base = degree f"
    "d.Span (rupture_surj K f ` poly_of_const ` K) base =
      carrier (Rupt K f)"
    using d.exists_base[OF b a] by auto
  have "order (Rupt K f) =
    card (d.Span (rupture_surj K f ` poly_of_const ` K) base)"
    unfolding order_def base_def(4) by simp
  also have "... =
    card (rupture_surj K f ` poly_of_const ` K) ^ length base"
    using d.card_span[OF b base_def(2,1)] by simp
  also have "...
    = card ((rupture_surj K f \<circ> poly_of_const) ` K) ^ degree f"
    using base_def(3) image_image unfolding comp_def by metis
  also have "... = card K^degree f"
    by (subst card_image[OF d], simp)
  finally show "order (Rupt K f) = card K^degree f" by simp

  have "char (Rupt K f) = char (R \<lparr> carrier := K \<rparr>)"
    using h.char_consistent d by simp
  also have "... = char R"
    using char_consistent[OF subfieldE(1)[OF assms(1)]] by simp
  finally show "char (Rupt K f) = char R" by simp
qed

definition gauss_poly where
  "gauss_poly K n = X\<^bsub>K\<^esub> [^]\<^bsub>poly_ring K\<^esub> (n::nat) \<ominus>\<^bsub>poly_ring K\<^esub> X\<^bsub>K\<^esub>"

context field
begin

interpretation polynomial_ring "R" "carrier R"
  unfolding polynomial_ring_def polynomial_ring_axioms_def
  using field_axioms carrier_is_subfield by simp

text \<open>The following lemma can be found in Ireland and Rosen~\<^cite>\<open>\<open>\textsection 7.1, Lemma 2\<close> in "ireland1982"\<close>.\<close>

lemma gauss_poly_div_gauss_poly_iff_1:
  fixes l m :: nat
  assumes "l > 0"
  shows "(X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides (X [^]\<^bsub>P\<^esub> m \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<longleftrightarrow> l dvd m"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  define q where "q = m div l"
  define r where "r = m mod l"
  have m_def: "m = q * l + r" and r_range: "r < l"
    using assms by (auto simp add:q_def r_def)

  have pow_sum_carr:"(\<Oplus>\<^bsub>P\<^esub>i\<in>{..<q}. (X [^]\<^bsub>P\<^esub> l)[^]\<^bsub>P\<^esub> i) \<in> carrier P"
    using var_pow_closed
    by (intro p.finsum_closed, simp)

  have "(X [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = ((X [^]\<^bsub>P\<^esub> l)[^]\<^bsub>P\<^esub> q) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    using var_closed
    by (subst p.nat_pow_pow, simp_all add:algebra_simps)
  also have "... =
    (X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> (\<Oplus>\<^bsub>P\<^esub>i\<in>{..<q}. (X [^]\<^bsub>P\<^esub> l) [^]\<^bsub>P\<^esub> i)"
    using var_pow_closed
    by (subst p.geom[symmetric], simp_all)
  finally have pow_sum_fact: "(X [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) =
    (X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> (\<Oplus>\<^bsub>P\<^esub>i\<in>{..<q}. (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l) [^]\<^bsub>P\<^esub> i)"
    by simp

  have "(X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) divides\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    by (rule dividesI[OF pow_sum_carr pow_sum_fact])

  hence c:"(X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) divides\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q * l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using var_pow_closed
    by (intro p.divides_prod_l, auto)

  have "(X [^]\<^bsub>P\<^esub> m \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = X [^]\<^bsub>P\<^esub> (r + q * l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    unfolding m_def using add.commute by metis
  also have "... = (X [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q*l)) \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using var_closed
    by (subst p.nat_pow_mult, auto simp add:a_minus_def)
  also have "... = ((X [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q*l) \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>))
    \<oplus>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> r)) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    using var_pow_closed
    by algebra
  also have "... = (X [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)
    \<oplus>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> r) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    by algebra
  also have "... = (X [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)
    \<oplus>\<^bsub>P\<^esub> ((X [^]\<^bsub>P\<^esub> r) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    unfolding a_minus_def using var_pow_closed
    by (subst p.a_assoc, auto)
  finally have a:"(X [^]\<^bsub>P\<^esub> m \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) =
    (X [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<oplus>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    (is "_ = ?x")
    by simp

  have xn_m_1_deg': "degree (X [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = n"
    if "n > 0" for n :: nat
  proof -
    have "degree (X [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = degree (X [^]\<^bsub>P\<^esub> n \<oplus>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      by (simp add:a_minus_def)
    also have "... = max (degree (X [^]\<^bsub>P\<^esub> n)) (degree (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>))"
      using var_pow_closed var_pow_carr var_pow_degree
      using univ_poly_a_inv_degree degree_one that
      by (subst degree_add_distinct, auto)
    also have "... = n"
      using var_pow_degree degree_one univ_poly_a_inv_degree
      by simp
    finally show ?thesis by simp
  qed

  have xn_m_1_deg: "degree (X [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = n" for n :: nat
  proof (cases "n > 0")
    case True
    then show ?thesis using xn_m_1_deg' by auto
  next
    case False
    hence "n = 0" by simp
    hence "degree (X [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = degree (\<zero>\<^bsub>P\<^esub>)"
      by (intro arg_cong[where f="degree"], simp)
    then show ?thesis using False by (simp add:univ_poly_zero)
  qed

  have b: "degree (X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) > degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using r_range unfolding xn_m_1_deg by simp

  have xn_m_1_carr: "X [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<in> carrier P" for n :: nat
    unfolding a_minus_def
    by (intro p.a_closed var_pow_closed, simp)

  have "?lhs \<longleftrightarrow> (X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides ?x"
    by (subst a, simp)
  also have "... \<longleftrightarrow> (X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides (X [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    unfolding pdivides_def
    by (intro p.div_sum_iff c var_pow_closed
        xn_m_1_carr p.a_closed p.m_closed)
  also have "... \<longleftrightarrow> r = 0"
  proof (cases "r = 0")
    case True
    have "(X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides \<zero>\<^bsub>P\<^esub>"
      unfolding univ_poly_zero
      by (intro pdivides_zero xn_m_1_carr)
    also have "... = (X [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      by (simp add:a_minus_def True) algebra
    finally show ?thesis using True by simp
  next
    case False
    hence "degree (X [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) > 0" using xn_m_1_deg by simp
    hence "X [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<noteq> []" by auto
    hence "\<not>(X [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides (X [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      using pdivides_imp_degree_le b xn_m_1_carr
      by (metis le_antisym less_or_eq_imp_le nat_neq_iff)
    thus ?thesis using False by simp
  qed
  also have "... \<longleftrightarrow> l dvd m"
    unfolding m_def using r_range assms by auto
  finally show ?thesis
    by simp
qed

lemma gauss_poly_factor:
  assumes "n > 0"
  shows "gauss_poly R n = (X [^]\<^bsub>P\<^esub> (n-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> X" (is "_ = ?rhs")
proof -
  have a:"1 + (n - 1) = n"
    using assms by simp
  have "gauss_poly R n = X [^]\<^bsub>P\<^esub> (1+(n-1)) \<ominus>\<^bsub>P\<^esub> X"
    unfolding gauss_poly_def by (subst a, simp)
  also have "... = (X [^]\<^bsub>P\<^esub> (n-1)) \<otimes>\<^bsub>P\<^esub> X \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<otimes>\<^bsub>P\<^esub> X"
    using var_closed by simp
  also have "... = ?rhs"
    unfolding a_minus_def using var_closed l_one
    by (subst p.l_distr, auto, algebra)
  finally show ?thesis by simp
qed

lemma var_neq_zero: "X \<noteq> \<zero>\<^bsub>P\<^esub>"
  by (simp add:var_def univ_poly_zero)

lemma var_pow_eq_one_iff: "X [^]\<^bsub>P\<^esub> k = \<one>\<^bsub>P\<^esub> \<longleftrightarrow> k = (0::nat)"
proof (cases "k=0")
  case True
  then show ?thesis using var_closed(1) by simp
next
  case False
  have "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> k) = k "
    using var_pow_degree by simp
  also have "... \<noteq> degree (\<one>\<^bsub>P\<^esub>)" using False degree_one by simp
  finally have "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> k) \<noteq> degree \<one>\<^bsub>P\<^esub>" by simp
  then show ?thesis by auto
qed

lemma gauss_poly_carr: "gauss_poly R n \<in> carrier P"
  using var_closed(1)
  unfolding gauss_poly_def by simp

lemma gauss_poly_degree:
  assumes "n > 1"
  shows "degree (gauss_poly R n) = n"
proof -
  have "degree (gauss_poly R n) = max n 1"
    unfolding gauss_poly_def a_minus_def
    using var_pow_carr var_carr degree_var
    using var_pow_degree univ_poly_a_inv_degree
    using assms by (subst degree_add_distinct, auto)
  also have "... = n" using assms by simp
  finally show ?thesis by simp
qed

lemma gauss_poly_not_zero:
  assumes "n > 1"
  shows "gauss_poly R n \<noteq> \<zero>\<^bsub>P\<^esub>"
proof -
  have "degree (gauss_poly R n) \<noteq> degree ( \<zero>\<^bsub>P\<^esub>)"
    using assms by (subst gauss_poly_degree, simp_all add:univ_poly_zero)
  thus ?thesis by auto
qed

lemma gauss_poly_monic:
  assumes "n > 1"
  shows "monic_poly R (gauss_poly R n)"
proof -
  have "monic_poly R (X [^]\<^bsub>P\<^esub> n)"
    by (intro monic_poly_pow monic_poly_var)
  moreover have "\<ominus>\<^bsub>P\<^esub> X \<in> carrier P"
    using var_closed by simp
  moreover have "degree (\<ominus>\<^bsub>P\<^esub> X) < degree (X [^]\<^bsub>P\<^esub> n)"
    using assms univ_poly_a_inv_degree var_closed
    using degree_var
    unfolding var_pow_degree by (simp)
  ultimately show ?thesis
    unfolding gauss_poly_def a_minus_def
    by (intro monic_poly_add_distinct, auto)
qed

lemma geom_nat:
  fixes q :: nat
  fixes x :: "_ :: {comm_ring,monoid_mult}"
  shows "(x-1) * (\<Sum>i \<in> {..<q}. x^i) = x^q-1"
  by (induction q, auto simp:algebra_simps)

text \<open>The following lemma can be found in Ireland and Rosen~\<^cite>\<open>\<open>\textsection 7.1, Lemma 3\<close> in "ireland1982"\<close>.\<close>

lemma gauss_poly_div_gauss_poly_iff_2:
  fixes a :: int
  fixes l m :: nat
  assumes "l > 0" "a > 1"
  shows "(a ^ l - 1) dvd (a ^ m - 1) \<longleftrightarrow> l dvd m"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  define q where "q = m div l"
  define r where "r = m mod l"
  have m_def: "m = q * l + r" and r_range: "r < l" "r \<ge> 0"
    using assms by (auto simp add:q_def r_def)

  have "a ^ (l * q) - 1 = (a ^ l) ^ q - 1"
    by (simp add: power_mult)
  also have "... = (a^l - 1) * (\<Sum>i \<in> {..<q}. (a^l)^i)"
    by (subst geom_nat[symmetric], simp)
  finally have "a ^ (l * q) - 1 = (a^l - 1) * (\<Sum>i \<in> {..<q}. (a^l)^i)"
    by simp
  hence c:"a ^ l - 1 dvd a^ r * (a ^ (q * l) - 1)" by (simp add:mult.commute)

  have "a ^ m - 1 = a ^ (r + q * l) - 1"
    unfolding m_def using add.commute by metis
  also have "... = (a ^ r) * (a ^ (q*l)) -1"
    by (simp add: power_add)
  also have "... = ((a ^ r) * (a ^ (q*l) -1)) + (a ^ r) - 1"
    by (simp add: right_diff_distrib)
  also have "... = (a ^ r) * (a ^ (q*l) - 1) + ((a ^ r) - 1)"
    by simp
  finally have a:
    "a ^ m - 1 = (a ^ r) * (a ^ (q*l) - 1) + ((a ^ r) - 1)"
    (is "_ = ?x")
    by simp

  have "?lhs \<longleftrightarrow> (a^l -1) dvd ?x"
    by (subst a, simp)
  also have "... \<longleftrightarrow> (a^l -1) dvd (a^r -1)"
    using c dvd_add_right_iff by auto
  also have "... \<longleftrightarrow> r = 0"
  proof
    assume "a ^ l - 1 dvd a ^ r - 1"
    hence "a ^ l - 1  \<le> a ^ r -1 \<or> r = 0 "
      using assms r_range zdvd_not_zless by force
    moreover have "a ^ r < a^l" using assms r_range by simp
    ultimately show "r= 0"by simp
  next
    assume "r = 0"
    thus "a ^ l - 1 dvd a ^ r - 1" by simp
  qed
  also have "... \<longleftrightarrow> l dvd m"
    using r_def by auto
  finally show ?thesis by simp
qed

lemma gauss_poly_div_gauss_poly_iff:
  assumes "m > 0" "n > 0" "a > 1"
  shows "gauss_poly R (a^n) pdivides\<^bsub>R\<^esub> gauss_poly R (a^m)
    \<longleftrightarrow> n dvd m" (is "?lhs=?rhs")
proof -
  have a:"a^m > 1" using assms one_less_power by blast
  hence a1: "a^m > 0" by linarith
  have b:"a^n > 1" using assms one_less_power by blast
  hence b1:"a^n > 0" by linarith

  have "?lhs \<longleftrightarrow>
    (X [^]\<^bsub>P\<^esub> (a^n-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> X pdivides
    (X [^]\<^bsub>P\<^esub> (a^m-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> X"
    using  gauss_poly_factor a1 b1 by simp
  also have "... \<longleftrightarrow>
    (X [^]\<^bsub>P\<^esub> (a^n-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides
    (X [^]\<^bsub>P\<^esub> (a^m-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using var_closed a b var_neq_zero
    by (subst pdivides_mult_r, simp_all add:var_pow_eq_one_iff)
  also have "... \<longleftrightarrow> a^n-1 dvd a^m-1"
    using b
    by (subst gauss_poly_div_gauss_poly_iff_1) simp_all
  also have "... \<longleftrightarrow> int (a^n-1) dvd int (a^m-1)"
    by (subst of_nat_dvd_iff, simp)
  also have "... \<longleftrightarrow> int a^n-1 dvd int a^m-1"
    using a b by (simp add:of_nat_diff)
  also have "... \<longleftrightarrow> n dvd m"
    using assms
    by (subst gauss_poly_div_gauss_poly_iff_2) simp_all
  finally show ?thesis by simp
qed

end

context finite_field
begin

interpretation polynomial_ring "R" "carrier R"
  unfolding polynomial_ring_def polynomial_ring_axioms_def
  using field_axioms carrier_is_subfield by simp

lemma div_gauss_poly_iff:
  assumes "n > 0"
  assumes "monic_irreducible_poly R f"
  shows "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n) \<longleftrightarrow> degree f dvd n"
proof -
  have f_carr: "f \<in> carrier P"
    using assms(2) unfolding monic_irreducible_poly_def
    unfolding monic_poly_def by simp
  have f_deg: "degree f > 0"
    using assms(2) monic_poly_min_degree by fastforce

  define K where "K = Rupt\<^bsub>R\<^esub> (carrier R) f"
  have field_K: "field K"
    using assms(2) unfolding K_def monic_irreducible_poly_def
    unfolding monic_poly_def
    by (subst rupture_is_field_iff_pirreducible)  auto
  have a: "order K = order R^degree f"
    using rupture_order[OF carrier_is_subfield] f_carr f_deg
    unfolding K_def order_def by simp
  have char_K: "char K = char R"
    using rupture_char[OF carrier_is_subfield] f_carr f_deg
    unfolding K_def by simp

  have "card (carrier K) > 0"
    using a f_deg finite_field_min_order unfolding order_def by simp
  hence d: "finite (carrier K)" using card_ge_0_finite by auto
  interpret f: finite_field "K"
    using field_K d by (intro finite_fieldI, simp_all)
  interpret fp: polynomial_ring "K" "(carrier K)"
    unfolding polynomial_ring_def polynomial_ring_axioms_def
    using f.field_axioms f.carrier_is_subfield by simp

  define \<phi> where "\<phi> = rupture_surj (carrier R) f"
  interpret h:ring_hom_ring "P" "K" "\<phi>"
    unfolding K_def \<phi>_def using f_carr rupture_surj_hom by simp

  have embed_inj: "inj_on (\<phi> \<circ> poly_of_const) (carrier R)"
    unfolding \<phi>_def
    using embed_inj[OF carrier_is_subfield f_carr f_deg] by simp

  interpret r:ring_hom_ring "R" "P" "poly_of_const"
    using canonical_embedding_ring_hom by simp

  obtain rn where "order R = char K^rn" "rn > 0"
    unfolding char_K using finite_field_order by auto
  hence ord_rn: "order R ^n = char K^(rn * n)" using assms(1)
    by (simp add: power_mult)

  interpret q:ring_hom_cring "K" "K" "\<lambda>x. x [^]\<^bsub>K\<^esub> order R^n"
    using ord_rn
    by (intro f.frobenius_hom f.finite_carr_imp_char_ge_0 d, simp)

  have o1: "order R^degree f > 1"
    using f_deg finite_field_min_order one_less_power
    by blast
  hence o11: "order R^degree f > 0" by linarith
  have o2: "order R^n > 1"
    using assms(1) finite_field_min_order one_less_power
    by blast
  hence o21: "order R^n > 0" by linarith
  let ?g1 = "gauss_poly K (order R^degree f)"
  let ?g2 = "gauss_poly K (order R^n)"

  have g1_monic: "monic_poly K ?g1"
    using f.gauss_poly_monic[OF o1] by simp

  have c:"x [^]\<^bsub>K\<^esub> (order R^degree f) = x" if b:"x \<in> carrier K" for x
    using b d order_pow_eq_self
    unfolding a[symmetric]
    by (intro f.order_pow_eq_self, auto)

  have k_cycle:
    "\<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> (order R^n) = \<phi>(poly_of_const x)"
    if k_cycle_1: "x \<in> carrier R" for x
  proof -
    have "\<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> (order R^n) =
      \<phi> (poly_of_const (x [^]\<^bsub>R\<^esub> (order R^n)))"
      using k_cycle_1 by (simp add: h.hom_nat_pow r.hom_nat_pow)
    also have "... = \<phi> (poly_of_const x)"
      using order_pow_eq_self' k_cycle_1 by simp
    finally show ?thesis by simp
  qed

  have roots_g1: "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
    if roots_g1_assms: "degree d = 1" "monic_irreducible_poly K d" for d
  proof -
    obtain x where x_def: "x \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x]"
      using f.degree_one_monic_poly roots_g1_assms by auto
    interpret x:ring_hom_cring "poly_ring K" "K" "(\<lambda>p. f.eval p x)"
      by (intro fp.eval_cring_hom x_def)
    have "ring.eval K ?g1 x = \<zero>\<^bsub>K\<^esub>"
      unfolding gauss_poly_def a_minus_def
      using fp.var_closed f.eval_var x_def c
      by (simp, algebra)
    hence "f.is_root ?g1 x"
      using x_def f.gauss_poly_not_zero[OF o1]
      unfolding f.is_root_def univ_poly_zero by simp
    hence "[\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x] pdivides\<^bsub>K\<^esub> ?g1"
      using f.is_root_imp_pdivides f.gauss_poly_carr by simp
    hence "d pdivides\<^bsub>K\<^esub> ?g1" by (simp add:x_def)
    thus "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
      using that f.gauss_poly_not_zero f.gauss_poly_carr o1
      by (subst f.multiplicity_ge_1_iff_pdivides, simp_all)
  qed

  show ?thesis
  proof
    assume f:"f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n)"
    have "(\<phi> X) [^]\<^bsub>K\<^esub> (order R^n) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>) =
      \<phi> (gauss_poly R (order R^n))"
      unfolding gauss_poly_def a_minus_def using var_closed
      by (simp add: h.hom_nat_pow)
    also have "... = \<zero>\<^bsub>K\<^esub>"
      unfolding K_def \<phi>_def using f_carr gauss_poly_carr f
      by (subst rupture_eq_0_iff, simp_all)
    finally have "(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>) = \<zero>\<^bsub>K\<^esub>"
      by simp
    hence g:"(\<phi> X) [^]\<^bsub>K\<^esub> (order R^n) = (\<phi> X)"
      using var_closed by simp

    have roots_g2: "pmult\<^bsub>K\<^esub> d ?g2 \<ge> 1"
      if roots_g2_assms: "degree d = 1" "monic_irreducible_poly K d" for d
    proof -
      obtain y where y_def: "y \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> y]"
        using f.degree_one_monic_poly roots_g2_assms by auto

      interpret x:ring_hom_cring "poly_ring K" "K" "(\<lambda>p. f.eval p y)"
        by (intro fp.eval_cring_hom y_def)
      obtain x where x_def: "x \<in> carrier P" "y = \<phi> x"
        using y_def unfolding \<phi>_def K_def rupture_def
        unfolding FactRing_def A_RCOSETS_def'
        by auto
      let ?\<tau>  = "\<lambda>i. poly_of_const (coeff x i)"
      have test: "?\<tau> i \<in> carrier P" for i
        by (intro r.hom_closed coeff_range x_def)
      have test_2: "coeff x i \<in> carrier R" for i
        by (intro coeff_range x_def)

      have x_coeff_carr: "i \<in> set x \<Longrightarrow> i \<in> carrier R"  for i
        using x_def(1)
        by (auto simp add:univ_poly_carrier[symmetric] polynomial_def)

      have a:"map (\<phi> \<circ> poly_of_const) x \<in> carrier (poly_ring K)"
        using rupture_surj_norm_is_hom[OF f_carr]
        using domain_axioms f.domain_axioms embed_inj
        by (intro carrier_hom'[OF  x_def(1)])
         (simp_all add:\<phi>_def K_def)

      have "(\<phi> x) [^]\<^bsub>K\<^esub> (order R^n) =
        f.eval (map (\<phi> \<circ> poly_of_const) x) (\<phi> X) [^]\<^bsub>K\<^esub> (order R^n)"
        unfolding \<phi>_def K_def
        by (subst rupture_surj_as_eval[OF f_carr x_def(1)], simp)
      also have "... =
        f.eval (map (\<lambda>x. \<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> order R ^ n) x) (\<phi> X)"
        using a h.hom_closed var_closed(1)
        by (subst q.ring.eval_hom[OF f.carrier_is_subring])
          (simp_all add:comp_def g)
      also have "... = f.eval (map (\<lambda>x. \<phi> (poly_of_const x)) x) (\<phi> X)"
        using k_cycle x_coeff_carr
        by (intro arg_cong2[where f="f.eval"] map_cong, simp_all)
      also have "... = (\<phi> x)"
        unfolding \<phi>_def K_def
        by (subst rupture_surj_as_eval[OF f_carr x_def(1)], simp add:comp_def)
      finally have "\<phi> x [^]\<^bsub>K\<^esub> order R ^ n = \<phi> x" by simp

      hence "y [^]\<^bsub>K\<^esub> (order R^n) = y" using x_def by simp
      hence "ring.eval K ?g2 y = \<zero>\<^bsub>K\<^esub>"
        unfolding gauss_poly_def a_minus_def
        using fp.var_closed f.eval_var y_def
        by (simp, algebra)
      hence "f.is_root ?g2 y"
        using y_def f.gauss_poly_not_zero[OF o2]
        unfolding f.is_root_def univ_poly_zero by simp
      hence "d pdivides\<^bsub>K\<^esub> ?g2"
        unfolding y_def
        by (intro f.is_root_imp_pdivides f.gauss_poly_carr, simp)
      thus "pmult\<^bsub>K\<^esub> d ?g2 \<ge> 1"
        using that f.gauss_poly_carr f.gauss_poly_not_zero o2
        by (subst f.multiplicity_ge_1_iff_pdivides, auto)
    qed

    have inv_k_inj: "inj_on (\<lambda>x. \<ominus>\<^bsub>K\<^esub> x) (carrier K)"
      by (intro inj_onI, metis f.minus_minus)
    let ?mip = "monic_irreducible_poly K"

    have "sum' (\<lambda>d. pmult\<^bsub>K\<^esub> d ?g1 * degree d) {d. ?mip d} = degree ?g1"
      using f.gauss_poly_monic o1
      by (subst f.degree_monic_poly', simp_all)
    also have "... = order K"
      using f.gauss_poly_degree o1 a by simp
    also have "... = card ((\<lambda>k. [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> k]) ` carrier K)"
      unfolding order_def using inj_onD[OF inv_k_inj]
      by (intro card_image[symmetric] inj_onI) (simp_all)
    also have "... = card {d. ?mip d \<and> degree d = 1}"
      using f.degree_one_monic_poly
      by (intro arg_cong[where f="card"], simp add:set_eq_iff image_iff)
    also have "... = sum (\<lambda>d. 1) {d. ?mip d \<and> degree d = 1}"
      by simp
    also have "... = sum' (\<lambda>d. 1) {d. ?mip d \<and> degree d = 1}"
      by (intro sum.eq_sum[symmetric]
          finite_subset[OF _ fp.finite_poly(1)[OF d]])
       (auto simp:monic_irreducible_poly_def monic_poly_def)
    also have "... = sum' (\<lambda>d. of_bool (degree d = 1)) {d. ?mip d}"
      by (intro sum.mono_neutral_cong_left' subsetI, simp_all)
    also have "... \<le> sum' (\<lambda>d. of_bool (degree d = 1)) {d. ?mip d}"
      by simp
    finally have "sum' (\<lambda>d. pmult\<^bsub>K\<^esub> d ?g1 * degree d) {d. ?mip d}
      \<le> sum' (\<lambda>d. of_bool (degree d = 1)) {d. ?mip d}"
      by simp
    moreover have
      "pmult\<^bsub>K\<^esub> d ?g1 * degree d \<ge> of_bool (degree d = 1)"
      if v:"monic_irreducible_poly K d" for d
    proof (cases "degree d = 1")
      case True
      then obtain x where "x \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x]"
        using f.degree_one_monic_poly v by auto
      hence "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
        using roots_g1 v by simp
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis by simp
    qed
    moreover have
      "finite {d. ?mip d \<and> pmult\<^bsub>K\<^esub> d ?g1 * degree d > 0}"
      by (intro finite_subset[OF _ f.factor_monic_poly_fin[OF g1_monic]]
          subsetI) simp
    ultimately have v2:
      "\<forall>d \<in> {d. ?mip d}. pmult\<^bsub>K\<^esub> d ?g1 * degree d =
      of_bool (degree d = 1)"
      by (intro sum'_eq_iff, simp_all add:not_le)
    have "pmult\<^bsub>K\<^esub> d ?g1 \<le> pmult\<^bsub>K\<^esub> d ?g2" if "?mip d" for d
    proof (cases "degree d = 1")
      case True
      hence "pmult\<^bsub>K\<^esub> d ?g1 = 1" using v2 that by auto
      also have "... \<le> pmult\<^bsub>K\<^esub> d ?g2"
        by (intro roots_g2 True that)
      finally show ?thesis by simp
    next
      case False
      hence "degree d > 1"
        using f.monic_poly_min_degree[OF that] by simp
      hence "pmult\<^bsub>K\<^esub> d ?g1 = 0" using v2 that by force
      then show ?thesis by simp
    qed
    hence "?g1 pdivides\<^bsub>K\<^esub> ?g2"
      using o1 o2 f.divides_monic_poly f.gauss_poly_monic by simp
    thus "degree f dvd n"
      by (subst (asm) f.gauss_poly_div_gauss_poly_iff
          [OF assms(1) f_deg finite_field_min_order], simp)
  next
    have d:"\<phi> X\<^bsub>R\<^esub> \<in> carrier K"
      by (intro h.hom_closed var_closed)

    have "\<phi> (gauss_poly R (order R^degree f)) =
      (\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^degree f) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>)"
      unfolding gauss_poly_def a_minus_def using var_closed
      by (simp add: h.hom_nat_pow)
    also have "... = \<zero>\<^bsub>K\<^esub>"
      using c d by simp
    finally have "\<phi> (gauss_poly R (order R^degree f)) = \<zero>\<^bsub>K\<^esub>" by simp
    hence "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^degree f)"
      unfolding K_def \<phi>_def using f_carr gauss_poly_carr
      by (subst (asm) rupture_eq_0_iff, simp_all)
    moreover assume "degree f dvd n"

    hence "gauss_poly R (order R^degree f) pdivides
      (gauss_poly R (order R^n))"
      using gauss_poly_div_gauss_poly_iff
        [OF assms(1) f_deg finite_field_min_order]
      by simp
    ultimately show "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n)"
      using f_carr a p.divides_trans unfolding pdivides_def by blast
  qed
qed

lemma gauss_poly_splitted:
  "splitted (gauss_poly R (order R))"
proof -
  have "degree q \<le> 1" if
    "q \<in> carrier P"
    "pirreducible (carrier R) q"
    "q pdivides gauss_poly R (order R)" for q
  proof -
    have q_carr: "q \<in> carrier (mult_of P)"
      using that unfolding ring_irreducible_def by simp
    moreover have "irreducible (mult_of P) q"
      using that unfolding ring_irreducible_def
      by (intro p.irreducible_imp_irreducible_mult that, simp_all)
    ultimately obtain p where p_def:
      "monic_irreducible_poly R p" "q \<sim>\<^bsub>mult_of P\<^esub> p"
      using monic_poly_span by auto
    have p_carr: "p \<in> carrier P" "p \<noteq> []"
      using p_def(1)
      unfolding monic_irreducible_poly_def monic_poly_def
      by auto
    moreover have "p divides\<^bsub>mult_of P\<^esub> q"
      using associatedE[OF p_def(2)] by auto
    hence "p pdivides q"
      unfolding pdivides_def using divides_mult_imp_divides by simp
    moreover have "q pdivides gauss_poly R (order R^1)"
      using that by simp
    ultimately have "p pdivides gauss_poly R (order R^1)"
      unfolding pdivides_def using p.divides_trans by blast
    hence "degree p dvd 1"
      using  div_gauss_poly_iff[where n="1"] p_def(1) by simp
    hence "degree p = 1" by simp
    moreover have "q divides\<^bsub>mult_of P\<^esub> p"
      using associatedE[OF p_def(2)] by auto
    hence "q pdivides p"
      unfolding pdivides_def using divides_mult_imp_divides by simp
    hence "degree q \<le> degree p"
      using that p_carr
      by (intro pdivides_imp_degree_le) auto
    ultimately show ?thesis by simp
  qed

  thus ?thesis
    using gauss_poly_carr
    by (intro trivial_factors_imp_splitted, auto)
qed

text \<open>The following lemma, for the case when @{term "R"} is a simple prime field, can be found in
Ireland and Rosen~\<^cite>\<open>\<open>\textsection 7.1, Theorem 2\<close> in "ireland1982"\<close>. Here the result is verified even
for arbitrary finite fields.\<close>

lemma multiplicity_of_factor_of_gauss_poly:
  assumes "n > 0"
  assumes "monic_irreducible_poly R f"
  shows
    "pmult\<^bsub>R\<^esub> f (gauss_poly R (order R^n)) = of_bool (degree f dvd n)"
proof (cases "degree f dvd n")
  case True
  let ?g = "gauss_poly R (order R^n)"
  have f_carr: "f \<in> carrier P" "f \<noteq> []"
    using assms(2)
    unfolding monic_irreducible_poly_def monic_poly_def
    by auto

  have o2: "order R^n > 1"
    using finite_field_min_order assms(1) one_less_power by blast
  hence o21: "order R^n > 0" by linarith

  obtain d :: nat where order_dim: "order R = char R ^ d" "d > 0"
    using finite_field_order by blast
  have "d * n > 0" using order_dim assms by simp
  hence char_dvd_order: "int (char R) dvd int (order R ^ n)"
    unfolding order_dim
    using finite_carr_imp_char_ge_0[OF finite_carrier]
    by (simp add:power_mult[symmetric])

  interpret h: ring_hom_ring  "R" "P" "poly_of_const"
    using canonical_embedding_ring_hom by simp

  have "f pdivides\<^bsub>R\<^esub> ?g"
    using True div_gauss_poly_iff[OF assms] by simp
  hence "pmult\<^bsub>R\<^esub> f ?g \<ge> 1"
    using multiplicity_ge_1_iff_pdivides[OF assms(2)]
    using gauss_poly_carr gauss_poly_not_zero[OF o2]
    by auto
  moreover have "pmult\<^bsub>R\<^esub> f ?g < 2"
  proof (rule ccontr)
    assume "\<not> pmult\<^bsub>R\<^esub> f ?g < 2"
    hence "pmult\<^bsub>R\<^esub> f ?g \<ge> 2" by simp
    hence "(f [^]\<^bsub>P\<^esub> (2::nat)) pdivides\<^bsub>R\<^esub> ?g"
      using gauss_poly_carr gauss_poly_not_zero[OF o2]
      by (subst (asm) multiplicity_ge_iff[OF assms(2)]) simp_all
    hence "(f [^]\<^bsub>P\<^esub> (2::nat)) divides\<^bsub>mult_of P\<^esub> ?g"
      unfolding pdivides_def
      using f_carr gauss_poly_not_zero o2 gauss_poly_carr
      by (intro p.divides_imp_divides_mult) simp_all
    then obtain h where h_def:
      "h \<in> carrier (mult_of P)"
      "?g = f [^]\<^bsub>P\<^esub> (2::nat) \<otimes>\<^bsub>P\<^esub> h"
      using dividesD by auto
    have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> = int_embed P (order R ^ n)
      \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (order R ^ n-1)) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
      using var_closed
      apply (subst int_embed_consistent_with_poly_of_const)
      apply (subst iffD2[OF embed_char_eq_0_iff char_dvd_order])
      by (simp add:a_minus_def)
    also have "... = pderiv\<^bsub>R\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> order R ^ n) \<ominus>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> X\<^bsub>R\<^esub>"
      using pderiv_var
      by (subst pderiv_var_pow[OF o21], simp)
    also have "... = pderiv\<^bsub>R\<^esub> ?g"
      unfolding gauss_poly_def a_minus_def using var_closed
      by (subst pderiv_add, simp_all add:pderiv_inv)
    also have "... = pderiv\<^bsub>R\<^esub> (f [^]\<^bsub>P\<^esub> (2::nat) \<otimes>\<^bsub>P\<^esub> h)"
      using h_def(2) by simp
    also have "... = pderiv\<^bsub>R\<^esub> (f [^]\<^bsub>P\<^esub> (2::nat)) \<otimes>\<^bsub>P\<^esub> h
      \<oplus>\<^bsub>P\<^esub> (f [^]\<^bsub>P\<^esub> (2::nat)) \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h"
      using f_carr h_def
      by (intro pderiv_mult, simp_all)
    also have "... = int_embed P 2 \<otimes>\<^bsub>P\<^esub> f  \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h
      \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h"
      using f_carr
      by (subst pderiv_pow, simp_all add:numeral_eq_Suc)
    also have "... = f \<otimes>\<^bsub>P\<^esub> (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h)
      \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> (f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)"
      using f_carr pderiv_carr h_def p.int_embed_closed
      apply (intro arg_cong2[where f="(\<oplus>\<^bsub>P\<^esub>)"])
      by (subst p.m_comm, simp_all add:p.m_assoc)
    also have "... = f \<otimes>\<^bsub>P\<^esub>
      (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)"
      using f_carr pderiv_carr h_def p.int_embed_closed
      by (subst p.r_distr, simp_all)
    finally have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> = f \<otimes>\<^bsub>P\<^esub>
      (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)"
      (is "_ = f \<otimes>\<^bsub>P\<^esub> ?q")
      by simp

    hence "f pdivides\<^bsub>R\<^esub> \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
      unfolding factor_def pdivides_def
      using f_carr pderiv_carr h_def p.int_embed_closed
      by auto
    moreover have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<noteq> \<zero>\<^bsub>P\<^esub>" by simp
    ultimately have  "degree f \<le> degree (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      using f_carr
      by (intro pdivides_imp_degree_le, simp_all add:univ_poly_zero)
    also have "... = 0"
      by (subst univ_poly_a_inv_degree, simp)
       (simp add:univ_poly_one)
    finally have "degree f = 0" by simp

    then show "False"
      using pirreducible_degree assms(2)
      unfolding monic_irreducible_poly_def monic_poly_def
      by fastforce
  qed
  ultimately have "pmult\<^bsub>R\<^esub> f ?g = 1" by simp
  then show ?thesis using True by simp
next
  case False
  have o2: "order R^n > 1"
    using finite_field_min_order assms(1) one_less_power by blast

  have "\<not>(f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n))"
    using div_gauss_poly_iff[OF assms] False by simp
  hence "pmult\<^bsub>R\<^esub> f (gauss_poly R (order R^n)) = 0"
    using multiplicity_ge_1_iff_pdivides[OF assms(2)]
    using gauss_poly_carr gauss_poly_not_zero[OF o2] leI less_one
    by blast
  then show ?thesis using False by simp
qed

text \<open>The following lemma, for the case when @{term "R"} is a simple prime field, can be found in Ireland
and Rosen~\<^cite>\<open>\<open>\textsection 7.1, Corollary 1\<close> in "ireland1982"\<close>. Here the result is verified even for
arbitrary finite fields.\<close>

lemma card_irred_aux:
  assumes "n > 0"
  shows "order R^n = (\<Sum>d | d dvd n. d *
    card {f. monic_irreducible_poly R f \<and> degree f = d})"
  (is "?lhs = ?rhs")
proof -
  let ?G = "{f. monic_irreducible_poly R f \<and> degree f dvd n}"

  let ?D = "{f. monic_irreducible_poly R f}"
  have a: "finite {d. d dvd n}" using finite_divisors_nat assms by simp
  have b: "finite {f. monic_irreducible_poly R f \<and> degree f = k}" for k
  proof -
    have "{f. monic_irreducible_poly R f \<and> degree f = k} \<subseteq>
      {f. f \<in> carrier P \<and> degree f \<le> k}"
      unfolding monic_irreducible_poly_def monic_poly_def by auto
    moreover have "finite {f. f \<in> carrier P \<and> degree f \<le> k}"
      using finite_poly[OF finite_carrier] by simp
    ultimately show ?thesis using finite_subset by simp
  qed

  have G_split: "?G =
    \<Union> {{f.  monic_irreducible_poly R f \<and> degree f = d} | d. d dvd n}"
    by auto
  have c: "finite ?G"
    using a b by (subst G_split, auto)
  have d: "order R^n > 1"
    using assms finite_field_min_order one_less_power by blast

  have "?lhs = degree (gauss_poly R (order R^n))"
    using d
    by (subst gauss_poly_degree, simp_all)
  also have "... =
    sum' (\<lambda>d. pmult\<^bsub>R\<^esub> d (gauss_poly R (order R^n)) * degree d) ?D"
    using d
    by (intro degree_monic_poly'[symmetric] gauss_poly_monic)
  also have "... = sum' (\<lambda>d. of_bool (degree d dvd n) * degree d) ?D"
    using multiplicity_of_factor_of_gauss_poly[OF assms]
    by (intro sum.cong', auto)
  also have "... = sum' (\<lambda>d. degree d) ?G"
    by (intro sum.mono_neutral_cong_right' subsetI, auto)
  also have "... = (\<Sum> d \<in> ?G. degree d)"
    using c by (intro sum.eq_sum, simp)
  also have "... =
    (\<Sum> f \<in> (\<Union> d \<in> {d. d dvd n}.
    {f. monic_irreducible_poly R f \<and> degree f = d}). degree f)"
    by (intro sum.cong, auto simp add:set_eq_iff)
  also have "... = (\<Sum>d | d dvd n. sum degree
    {f. monic_irreducible_poly R f \<and> degree f = d})"
    using a b by (subst sum.UNION_disjoint, auto simp add:set_eq_iff)
  also have "... = (\<Sum>d | d dvd n. sum (\<lambda>_. d)
    {f. monic_irreducible_poly R f \<and> degree f = d})"
    by (intro sum.cong, simp_all)
  also have "... = ?rhs"
    by (simp add:mult.commute)
  finally show ?thesis
    by simp
qed

end

end
