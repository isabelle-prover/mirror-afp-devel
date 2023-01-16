section \<open>Bounded Degree Polynomials\<close>

text \<open>This section contains a definition for the set of polynomials with a degree bound and
establishes its cardinality.\<close>

theory Bounded_Degree_Polynomials
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

lemma (in ring) coeff_in_carrier: "p \<in> carrier (poly_ring R) \<Longrightarrow> coeff p i \<in> carrier R"
  using poly_coeff_in_carrier carrier_is_subring by (simp add: univ_poly_carrier)

definition bounded_degree_polynomials
  where "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> (degree x < n \<or> x = [])}"

text \<open>Note: The definition for @{term "bounded_degree_polynomials"} includes the zero polynomial
in @{term "bounded_degree_polynomials F 0"}. The reason for this adjustment is that, contrary to
definition in HOL Algebra, most authors set the degree of the zero polynomial to
$-\infty$~\<^cite>\<open>\<open>\textsection 7.2.2\<close> in "shoup2009computational"\<close>. That
definition make some identities, such as $\mathrm{deg}(f g) = \mathrm{deg}\, f + \mathrm{deg}\, g$
for polynomials $f$ and $g$ unconditionally true.
In particular, it prevents an unnecessary corner case in the statement of the results established
in this entry.\<close>

lemma bounded_degree_polynomials_length:
  "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> length x \<le> n}"
  unfolding bounded_degree_polynomials_def using leI order_less_le_trans by fastforce

lemma (in ring) fin_degree_bounded:
  assumes "finite (carrier R)"
  shows "finite (bounded_degree_polynomials R n)"
proof -
  have "bounded_degree_polynomials R n \<subseteq> {p. set p \<subseteq> carrier R \<and> length p \<le> n}"
    unfolding bounded_degree_polynomials_length
    using assms polynomial_incl univ_poly_carrier by blast
  thus ?thesis
    using assms finite_lists_length_le finite_subset by fast
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

  have a:"?A \<subseteq> (f ` ({0..<n}  \<rightarrow>\<^sub>E B))"
    unfolding f_def
    by (rule in_image_by_witness[where g="\<lambda>f. restrict f {0..<n}"], auto)

  have b:"(f ` ({0..<n}  \<rightarrow>\<^sub>E B)) \<subseteq> ?A"
    using f_def assms by auto

  have c: "inj_on f ({0..<n} \<rightarrow>\<^sub>E B)"
    by (rule inj_onI, metis PiE_E atLeastLessThan_iff ext f_def)

  have "card ?A = card (f ` ({0..<n}  \<rightarrow>\<^sub>E B))"
    using a b by auto
  also have "... = card ({0..<n} \<rightarrow>\<^sub>E B)"
    by (metis c card_image)
  also have "... = card B ^ n"
    by (simp add: card_PiE[OF finite_atLeastLessThan])
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

lemma (in ring) length_build_poly:
  "length (build_poly f n) \<le> n"
  by (metis length_map build_poly_def normalize_length_le length_rev length_upt
      less_imp_diff_less linorder_not_less)

lemma (in ring) build_poly_degree:
  "degree (build_poly f n) \<le> n-1"
  using length_build_poly diff_le_mono by presburger

lemma (in ring) build_poly_poly:
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> carrier R"
  shows "build_poly f n \<in> carrier (poly_ring R)"
  unfolding build_poly_def univ_poly_carrier[symmetric]
  by (rule normalize_gives_polynomial, simp add:image_subset_iff Ball_def assms)

lemma (in ring) build_poly_coeff:
  "coeff (build_poly f n) i = (if i < n then f i else \<zero>)"
proof -
  show "coeff (build_poly f n) i = (if i < n then f i else \<zero>)"
    unfolding build_poly_def normalize_coeff[symmetric]
    by (cases "i < n", (simp add:coeff_nth rev_nth coeff_length)+)
qed

lemma (in ring) build_poly_bounded:
  assumes "\<And>k. k < n \<Longrightarrow> f k \<in> carrier R"
  shows "build_poly f n \<in> bounded_degree_polynomials R n"
  unfolding bounded_degree_polynomials_length
  using build_poly_poly[OF assms] length_build_poly by auto

text \<open>The following establishes the total number of polynomials with a degree less than $n$.
Unlike the results in the following sections, it is already possible to establish this property for
polynomials with coefficients in a ring.\<close>

lemma (in ring) bounded_degree_polynomials_card:
  "card (bounded_degree_polynomials R n) = card (carrier R) ^ n"
proof -
  have a:"coeff ` bounded_degree_polynomials R n \<subseteq> {f. range f \<subseteq> (carrier R) \<and> (\<forall>k \<ge> n. f k = \<zero>)}"
    by (rule image_subsetI, auto simp add:bounded_degree_polynomials_def coeff_length coeff_in_carrier)

  have b:"{f. range f \<subseteq> (carrier R) \<and> (\<forall>k \<ge> n. f k = \<zero>)} \<subseteq> coeff ` bounded_degree_polynomials R n"
    apply (rule in_image_by_witness[where g="\<lambda>x. build_poly x n"])
    by (auto simp add:build_poly_coeff intro:build_poly_bounded)

  have "inj_on coeff (carrier (poly_ring R))"
    by (rule inj_onI, simp add: coeff_iff_polynomial_cond univ_poly_carrier)

  hence coeff_inj: "inj_on coeff (bounded_degree_polynomials R n)"
    using inj_on_subset bounded_degree_polynomials_def by blast

  have "card ( bounded_degree_polynomials R n) = card (coeff `  bounded_degree_polynomials R n)"
    using coeff_inj card_image[symmetric] by blast
  also have "... = card {f. range f \<subseteq> (carrier R) \<and> (\<forall>k \<ge> n. f k = \<zero>)}"
    by (rule arg_cong[where f="card"], rule order_antisym[OF a b])
  also have "... = card (carrier R)^n"
    by (rule card_mostly_constant_maps, simp)
  finally show ?thesis by simp
qed

end