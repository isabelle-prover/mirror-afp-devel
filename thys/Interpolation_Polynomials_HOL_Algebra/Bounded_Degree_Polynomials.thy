section \<open>Bounded Degree Polynomials\<close>

text \<open>This section contains a definition for the set of polynomials with a degree bound and
establishes its cardinality.\<close>

theory Bounded_Degree_Polynomials
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

lemma (in ring) coeff_in_carrier: "p \<in> carrier (poly_ring R) \<Longrightarrow> coeff p i \<in> carrier R"
  using poly_coeff_in_carrier carrier_is_subring  by (simp add: univ_poly_carrier)

definition bounded_degree_polynomials
  where "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> (degree x < n \<or> x = [])}"

text \<open>Note: The definition for @{term "bounded_degree_polynomials"} includes the zero polynomial
in @{term "bounded_degree_polynomials F 0"}. The reason for this adjustment is that, contrary to
definition in HOL Algebra, most authors set the degree of the zero polynomial to 
$-\infty$~\cite[\textsection 7.2.2]{shoup2009computational}. That
definition make some identities, such as $\mathrm{deg}(f g) = \mathrm{deg}\, f + \mathrm{deg}\, g$
for polynomials $f$ and $g$ unconditionally true.
In particular, it prevents an unnecessary corner case in the statement of the results established 
in this entry.\<close>

lemma bounded_degree_polynomials_length:
  "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> length x \<le> n}"
  apply (simp add:bounded_degree_polynomials_def)
  apply (rule Collect_cong)
  by (metis Suc_pred length_greater_0_conv less_Suc_eq_0_disj less_Suc_eq_le linorder_not_le)

lemma (in ring) fin_degree_bounded:
  assumes "finite (carrier R)"
  shows "finite (bounded_degree_polynomials R n)"
proof -
  have "bounded_degree_polynomials R n \<subseteq> {p. set p \<subseteq> carrier R \<and> length p \<le> n}"
    apply (rule subsetI)
    apply (simp add: bounded_degree_polynomials_length) using assms(1) 
    by (meson polynomial_incl univ_poly_carrier)
  thus ?thesis  apply (rule finite_subset)
    using assms(1) finite_lists_length_le by auto
qed

lemma (in ring) non_empty_bounded_degree_polynomials:
  "bounded_degree_polynomials R k \<noteq> {}"
proof -
  have "\<zero>\<^bsub>poly_ring R\<^esub> \<in> bounded_degree_polynomials R k"
    by (simp add: bounded_degree_polynomials_def univ_poly_zero univ_poly_zero_closed)
  thus ?thesis by auto
qed

lemma in_image_by_witness:
  assumes "\<And>x. x \<in> A \<Longrightarrow> g x \<in> B \<and> f (g x) = x"
  shows "A \<subseteq> f ` B"
  by (metis assms image_eqI subsetI)

lemma card_mostly_constant_maps:
  assumes "y \<in> B"
  shows "card {f. range f \<subseteq> B \<and> (\<forall>x. x \<ge> n \<longrightarrow> f x = y)} = card B ^ n" (is "card ?A = ?B") 
proof -
  define f where "f = (\<lambda>f k. if k < n then f k else y)"

  have "card ?A = card (f ` ({0..<n}  \<rightarrow>\<^sub>E B))"
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym) (* TODO Split *)
     apply (rule in_image_by_witness[where g="\<lambda>f. restrict f {0..<n}"])
     apply (rule conjI, simp add: range_subsetD)
     apply (rule ext, simp add:restrict_def Pi_def PiE_def f_def)
    apply (rule image_subsetI, simp add:f_def)
    apply (rule conjI) 
     apply (metis Int_iff PiE PiE_def atLeastLessThan_iff image_Collect_subsetI less_eq_nat.simps(1))
    by (rule image_subsetI, rule assms)
  also have "... = card ({0..<n} \<rightarrow>\<^sub>E B)"
    apply (rule card_image, rule inj_onI, rule ext, simp add:f_def)
    by (metis PiE_arb atLeastLessThan_iff)
  also have "... = card B ^ n"
    by (subst card_PiE, simp, simp)
  finally show ?thesis by simp
qed

definition (in ring) build_poly where
  "build_poly f n = normalize (rev (map f [0..<n]))"

lemma (in ring) poly_degree_bound_from_coeff:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "\<And>k. k \<ge> n \<Longrightarrow> coeff x k = \<zero>"
  shows "degree x < n \<or> x = \<zero>\<^bsub>poly_ring R\<^esub>"
proof (rule ccontr)
  assume a:"\<not>(degree x < n \<or> x = \<zero>\<^bsub>poly_ring R\<^esub>)"
  hence b:"lead_coeff x \<noteq> \<zero>\<^bsub>R\<^esub>" 
    by (metis assms(1) polynomial_def univ_poly_carrier univ_poly_zero)
  hence "coeff x (degree x) \<noteq> \<zero>" 
    by (metis a lead_coeff_simp univ_poly_zero)
  moreover have "degree x \<ge> n" by (meson a not_le)
  ultimately show "False" using assms(2) by blast
qed          

lemma (in ring) poly_degree_bound_from_coeff_1:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "\<And>k. k \<ge> n \<Longrightarrow> coeff x k = \<zero>"
  shows "x \<in> bounded_degree_polynomials R n"
  using poly_degree_bound_from_coeff[OF assms]
  by (simp add:bounded_degree_polynomials_def univ_poly_zero assms)

lemma (in ring)
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> carrier R"
  shows 
    build_poly_poly: "build_poly f n \<in> carrier (poly_ring R)" and
    build_poly_coeff: "\<And>i. coeff (build_poly f n) i = (if i < n then f i else \<zero>)" and
    build_poly_degree: "degree (build_poly f n) \<le> n - 1"
proof -
  show a:"build_poly f n \<in> carrier (poly_ring R)"
    apply (simp add:build_poly_def univ_poly_carrier[symmetric])
    apply (rule normalize_gives_polynomial, simp)
    using assms atLeastLessThan_iff by blast

  show b:"\<And>i. coeff (build_poly f n) i = (if i < n then f i else \<zero>)"
  proof -
    fix i :: nat
    show "coeff (build_poly f n) i = (if i < n then f i else \<zero>)"
      apply (cases "i < n")
      apply (simp add:build_poly_def normalize_coeff[symmetric])
       apply (subst coeff_nth, simp, simp add:rev_nth)
      apply (simp add:build_poly_def normalize_coeff[symmetric])
      by (subst coeff_length, simp, simp)
  qed

  have "degree (build_poly f n) < n \<or> build_poly f n = \<zero>\<^bsub>poly_ring R\<^esub>"
    apply (rule poly_degree_bound_from_coeff[OF a])
    using b by simp

  thus "degree (build_poly f n) \<le> n - 1"
    apply (cases n, simp add:build_poly_def)
    by (metis diff_Suc_1 diff_is_0_eq less_Suc_eq_le list.size(3) univ_poly_zero zero_diff)
qed

lemma (in ring) length_build_poly: 
  "length (build_poly f n) \<le> n"
  apply (simp add:build_poly_def)
  by (metis length_map normalize_length_le length_rev length_upt less_imp_diff_less linorder_not_less)

text \<open>The following establishes the total number of polynomials with a degree less than $n$.
Unlike the results in the following sections, it is already possible to establish this property for 
polynomials with coefficients in a ring.\<close>

lemma (in ring) bounded_degree_polynomials_card:
  "card (bounded_degree_polynomials R n) = card (carrier R) ^ n"
proof -
  have a:"coeff ` bounded_degree_polynomials R n \<subseteq> {f. range f \<subseteq> (carrier R) \<and> (\<forall>k \<ge> n. f k = \<zero>)}"
    apply (rule image_subsetI, simp add:bounded_degree_polynomials_def, rule conjI) 
    using coeff_length coeff_in_carrier by auto

  have b:"{f. range f \<subseteq> (carrier R) \<and> (\<forall>k \<ge> n. f k = \<zero>)} \<subseteq> coeff ` bounded_degree_polynomials R n"
    apply (rule in_image_by_witness[where g="\<lambda>x. build_poly x n"])
    apply (rule conjI, rule poly_degree_bound_from_coeff_1)
      apply (rule build_poly_poly, blast) 
     apply (subst coeff_length, metis length_build_poly order_trans, simp)
    by (rule ext, subst build_poly_coeff, blast, simp)

  have "card ( bounded_degree_polynomials R n) = card (coeff `  bounded_degree_polynomials R n)"
    apply (rule card_image[symmetric])
    apply (rule inj_on_subset[where A="carrier (poly_ring R)"])
     apply (rule inj_onI, simp add: coeff_iff_polynomial_cond univ_poly_carrier)
    by (simp add:bounded_degree_polynomials_def)
  also have "... = card {f. range f \<subseteq> (carrier R) \<and> (\<forall>k \<ge> n. f k = \<zero>)}"
    by (rule arg_cong[where f="card"], rule order_antisym[OF a b])
  also have "... = card (carrier R)^n" 
    by (rule card_mostly_constant_maps, simp)
  finally show ?thesis by simp
qed

end