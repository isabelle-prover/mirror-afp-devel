section \<open>Cardinalities of Interpolation Polynomials\<close>

text \<open>This section establishes the cardinalities of the set of polynomials with a degree bound
interpolating a given set of points.\<close>

theory Interpolation_Polynomial_Cardinalities
  imports Bounded_Degree_Polynomials Lagrange_Interpolation
begin

lemma (in ring) poly_add_coeff:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier (poly_ring R)"
  shows "coeff (x \<oplus>\<^bsub>poly_ring R\<^esub> y) k = coeff x k \<oplus> coeff y k"
  by (metis assms univ_poly_carrier polynomial_incl univ_poly_add poly_add_coeff)

lemma (in domain) poly_neg_coeff:
  assumes "x \<in> carrier (poly_ring R)"
  shows "coeff (\<ominus>\<^bsub>poly_ring R\<^esub> x) k = \<ominus>coeff x k"
proof -
  interpret x:cring "poly_ring R"
    using assms cring_def carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  have a:"\<zero>\<^bsub>poly_ring R\<^esub> = x \<ominus>\<^bsub>poly_ring R\<^esub> x"
    by (metis x.r_right_minus_eq assms(1))

  have "\<zero> = coeff (\<zero>\<^bsub>poly_ring R\<^esub>) k" by (simp add:univ_poly_zero)
  also have "... = coeff x k \<oplus> coeff (\<ominus>\<^bsub>poly_ring R\<^esub> x) k" using a assms
    by (simp add:a_minus_def poly_add_coeff)
  finally have "\<zero> = coeff x k \<oplus> coeff (\<ominus>\<^bsub>poly_ring R\<^esub> x) k" by simp
  thus ?thesis
    by (metis local.minus_minus x.a_inv_closed sum_zero_eq_neg coeff_in_carrier assms)
qed

lemma (in domain) poly_substract_coeff:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier (poly_ring R)"
  shows "coeff (x \<ominus>\<^bsub>poly_ring R\<^esub> y) k = coeff x k \<ominus> coeff y k"
proof -
  interpret x:cring "poly_ring R"
    using assms cring_def carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  show ?thesis
    using assms by (simp add:a_minus_def poly_add_coeff poly_neg_coeff)
qed

text \<open>A polynomial with more zeros than its degree is the zero polynomial.\<close>

lemma (in field) max_roots:
  assumes "p \<in> carrier (poly_ring R)"
  assumes "K \<subseteq> carrier R"
  assumes "finite K"
  assumes "degree p < card K"
  assumes "\<And>x. x \<in> K \<Longrightarrow> eval p x = \<zero>"
  shows "p = \<zero>\<^bsub>poly_ring R\<^esub>"
proof (rule ccontr)
  assume "p \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>"
  hence a:"p \<noteq> []" by (simp add: univ_poly_zero)
  have "\<And>x. count (mset_set K) x \<le> count (roots p) x"
  proof -
    fix x
    show "count (mset_set K) x \<le> count (roots p) x"
    proof (cases "x \<in> K")
      case True
      hence "is_root p x"
        by (meson a assms(2,5) is_ring is_root_def subsetD)
      hence "x \<in> set_mset (roots p)"
        using assms(1) roots_mem_iff_is_root field_def by force
      hence "1 \<le> count (roots p) x" by simp
      moreover have "count (mset_set K) x = 1" using True assms(3) by simp
      ultimately show ?thesis by presburger
    next
      case False
      hence "count (mset_set K) x = 0" by simp
      then show ?thesis by presburger
    qed
  qed
  hence "mset_set K \<subseteq># roots p"
    by (simp add: subseteq_mset_def)
  hence "card K \<le> size (roots p)"
    by (metis size_mset_mono size_mset_set)
  moreover have "size (roots p) \<le> degree p"
    using a size_roots_le_degree assms by auto
  ultimately show "False" using assms(4)
    by (meson leD less_le_trans)
qed

definition (in ring) split_poly
  where "split_poly K p = (restrict (eval p) K, \<lambda>k. coeff p (k+card K))"

text \<open>To establish the count of the number of polynomials of degree less than
$n$ interpolating a function $f$ on $K$ where $\lvert K \rvert \leq n$, the function
@{term "split_poly K"} establishes a bijection between the polynomials of degree less than
$n$ and the values of the polynomials on $K$ in combination with the coefficients of order
$\lvert K \rvert$ and greater.

For the injectivity: Note that the difference of two polynomials whose coefficients of order
$\lvert K \rvert$ and larger agree must have a degree less than $\lvert K \rvert$ and because
their values agree on $k$ points, it must have $\lvert K \rvert$ zeros and hence is the zero
polynomial.

For the surjectivty: Let $p$ be a polynomial whose coefficients larger than $\lvert K \rvert$ are
chosen, and all other coefficients be $0$. Now it is possible to find a polynomial $q$ interpolating
$f - p$ on $K$ using Lagrange interpolation. Then $p + q$ will interpolate $f$ on $K$ and because
the degree of $q$ is less than $\lvert K \rvert$ its coefficients of order $\lvert K \rvert$ will
be the same as those of $p$.

A tempting question is whether it would be easier to instead establish a bijection between the
polynomials of degree less than $n$ and its values on $K \cup K'$ where $K'$ are arbitrarily chosen
$n-\lvert K \rvert$ points in the field. This approach is indeed easier, however, it fails for
the case where the size of the field is less than $n$.\<close>

lemma (in field) split_poly_inj:
  assumes "finite K"
  assumes "K \<subseteq> carrier R"
  shows "inj_on (split_poly K) (carrier (poly_ring R))"
proof
  fix x
  fix y
  assume a1:"x \<in> carrier (poly_ring R)"
  assume a2:"y \<in> carrier (poly_ring R)"
  assume a3:"split_poly K x = split_poly K y"

  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  have x_y_carrier: "x \<ominus>\<^bsub>poly_ring R\<^esub> y \<in> carrier (poly_ring R)" using a1 a2 by simp
  have "\<And>k. coeff x (k+card K) = coeff y (k+card K)"
    using a3 by (simp add:split_poly_def, meson)
  hence "\<And>k. coeff (x \<ominus>\<^bsub>poly_ring R\<^esub> y) (k+card K) = \<zero>"
    using coeff_in_carrier a1 a2 by (simp add:poly_substract_coeff)
  hence "degree (x \<ominus>\<^bsub>poly_ring R\<^esub> y) < card K \<or> (x \<ominus>\<^bsub>poly_ring R\<^esub> y) = \<zero>\<^bsub>poly_ring R\<^esub>"
    by (metis poly_degree_bound_from_coeff add.commute le_iff_add x_y_carrier)
  moreover have "\<And>k. k \<in> K \<Longrightarrow> eval x k = eval y k"
    using a3 by (simp add:split_poly_def restrict_def, meson)
  hence "\<And>k. k \<in> K \<Longrightarrow> eval x k \<ominus> eval y k = \<zero>"
    by (metis eval_in_carrier univ_poly_carrier polynomial_incl a1 assms(2) in_mono r_right_minus_eq)
  hence "\<And>k. k \<in> K \<Longrightarrow> eval (x \<ominus>\<^bsub>poly_ring R\<^esub> y) k = \<zero>"
    using a1 a2 subsetD[OF assms(2)] carrier_is_subring
    by (simp add: ring_hom_cring.hom_sub[OF eval_cring_hom])
  ultimately have "x \<ominus>\<^bsub>poly_ring R\<^esub> y = \<zero>\<^bsub>poly_ring R\<^esub>"
    using max_roots x_y_carrier assms by blast
  then show "x = y"
    using x.r_right_minus_eq[OF a1 a2] by simp
qed

lemma (in field) split_poly_image:
  assumes "finite K"
  assumes "K \<subseteq> carrier R"
  shows "split_poly K ` carrier (poly_ring R) \<supseteq>
        (K \<rightarrow>\<^sub>E carrier R) \<times> {f. range f \<subseteq> carrier R \<and> (\<exists>n. \<forall>k \<ge> n. f k = \<zero>\<^bsub>R\<^esub>)}"
proof (rule subsetI)
  fix x
  assume a:"x \<in> (K \<rightarrow>\<^sub>E carrier R) \<times> {f. range f \<subseteq> carrier R \<and> (\<exists>(n::nat). \<forall>k \<ge> n. f k = \<zero>)}"
  have a1: "fst x \<in> (K \<rightarrow>\<^sub>E carrier R)"
    using a by (simp add:mem_Times_iff)
  obtain n where a2: "snd x \<in> {f. range f \<subseteq> carrier R \<and> (\<forall>k \<ge> n. f k = \<zero>)}"
    using a mem_Times_iff by force
  have a3: "\<And>y. snd x y \<in> carrier R" using a2 by blast

  define w where "w = build_poly (\<lambda>i. if i \<ge> card K then (snd x (i - card K)) else \<zero>) (card K + n)"

  have w_carr: "w \<in> carrier (poly_ring R)"
    unfolding w_def by (rule build_poly_poly, simp add:a3)

  have w_eval_range: "\<And>x. x \<in> carrier R \<Longrightarrow> local.eval w x \<in> carrier R"
  proof -
    fix x
    assume w_eval_range_1:"x \<in> carrier R"
    interpret x:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p x)"
      using eval_cring_hom[OF carrier_is_subring] assms w_eval_range_1 by blast
    show "eval w x \<in> carrier R"
      by (rule x.hom_closed[OF w_carr])
  qed

  interpret r:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  define y where "y = interpolate K (\<lambda>k. fst x k \<ominus> eval w k)"
  define r where "r = y \<oplus>\<^bsub>poly_ring R\<^esub> w"

  have x_minus_w_in_carrier: "\<And>z. z \<in> K \<Longrightarrow> fst x z \<ominus> eval w z \<in> carrier R"
    using a1 PiE_def Pi_def minus_closed subsetD[OF assms(2)] w_eval_range by auto

  have y_poly: "y \<in> carrier (poly_ring R)" unfolding y_def
    using x_minus_w_in_carrier interpolate_poly[OF assms(1) assms(2)] image_subsetI by force

  have y_degree: "degree y \<le> card K - 1"
    unfolding y_def
    using x_minus_w_in_carrier interpolate_degree[OF assms(1) assms(2)] image_subsetI by force

  have y_len: "length y \<le> card K"
  proof (cases "K={}")
    case True
    then show ?thesis
      by (simp add:y_def interpolate_def univ_poly_zero)
  next
    case False
    then show ?thesis
      by (metis y_degree Suc_le_D assms(1) card_gt_0_iff diff_Suc_1 not_less_eq_eq order.strict_iff_not)
  qed

  have r_poly: "r \<in> carrier (poly_ring R)"
    using r_def y_poly w_carr by simp

  have coeff_r: "\<And>k. coeff r (k + card K) = snd x k"
  proof -
    fix k :: nat
    have y_len': "length y \<le> k + card K" using y_len trans_le_add2 by blast
    have "coeff r (k + card K) = coeff y (k + card K) \<oplus> coeff w (k+card K)"
      by (simp add:r_def  poly_add_coeff[OF y_poly w_carr])
    also have "... = \<zero> \<oplus> coeff w (k+card K)"
      using coeff_length[OF y_len'] by simp
    also have "... = coeff w (k+card K)"
      using coeff_in_carrier[OF w_carr] by simp
    also have "... = snd x k"
      using a2 by (simp add:w_def build_poly_coeff not_less)
    finally show "coeff r (k + card K) = snd x k" by simp
  qed

  have eval_r: "\<And>k. k \<in> K \<Longrightarrow> eval r k = fst x k"
  proof -
    fix k
    assume b:"k \<in> K"
    interpret s:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p k)"
      using eval_cring_hom[OF carrier_is_subring] assms b by blast

    have k_carr: "k \<in> carrier R" using assms(2) b by blast
    have fst_x_k_carr: "\<And>k. k \<in> K \<Longrightarrow> fst x k \<in> carrier R"
      using  a1 PiE_def Pi_def by blast
    have "eval r k = eval y k \<oplus> eval w k"
      using y_poly w_carr by (simp add:r_def)
    also have "... = fst x k \<ominus> local.eval w k \<oplus> local.eval w k"
      using assms b x_minus_w_in_carrier
      by (simp add:y_def interpolate_eval[OF _ _ image_subsetI])
    also have "... = fst x k \<oplus> (\<ominus> local.eval w k \<oplus> local.eval w k)"
      using fst_x_k_carr[OF b] w_eval_range[OF k_carr]
      by (simp add:a_minus_def a_assoc)
    also have "... = fst x k"
      using fst_x_k_carr[OF b] w_eval_range[OF k_carr]
      by (simp add:a_comm r_neg)
    finally show "eval r k = fst x k" by simp
  qed

  have "r \<in> (carrier (poly_ring R))"
    by (metis r_poly)
  moreover have "\<And>y. (if y \<in> K then eval r y else undefined) = fst x y"
    using a1 eval_r PiE_E by auto
  hence "split_poly K r = x"
    by (simp add:split_poly_def prod_eq_iff coeff_r restrict_def)
  ultimately show "x \<in> split_poly K ` (carrier (poly_ring R))"
    by blast
qed

text \<open>This is like @{thm [source] card_vimage_inj} but supports @{term "inj_on"} instead.\<close>
lemma card_vimage_inj_on:
  assumes "inj_on f B"
  assumes "A \<subseteq> f ` B"
  shows "card (f -` A \<inter> B) = card A"
proof -
  have "A = f ` (f -` A \<inter> B)" using assms(2) by auto
  thus ?thesis using assms card_image
    by (metis inf_le2 inj_on_subset)
qed

lemma inv_subsetI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> x \<in> C"
  shows "f -` B \<inter> A \<subseteq> C"
  using assms by force

text \<open>The following establishes the main result of this section: There are $\lvert F \rvert^{n-k}$
polynomials of degree less than $n$ interpolating $k \leq n$ points.\<close>

lemma restrict_eq_imp:
  assumes "restrict f A = restrict g A"
  assumes "x \<in> A"
  shows "f x = g x"
  by (metis restrict_def assms)

theorem (in field) interpolating_polynomials_card:
  assumes "finite K"
  assumes "K \<subseteq> carrier R"
  assumes "f ` K \<subseteq> carrier R"
  shows "card {\<omega> \<in> bounded_degree_polynomials R (card K + n). (\<forall>k \<in> K. eval \<omega> k = f k)} = card (carrier R)^n"
    (is "card ?A = ?B")
proof -
  define z where "z = restrict f K"
  define M where "M = {f. range f \<subseteq> carrier R \<and> (\<forall>k \<ge> n. f k = \<zero>)}"

  hence inj_on_bounded: "inj_on (split_poly K) (carrier (poly_ring R))"
    using split_poly_inj[OF assms(1) assms(2)] by blast

  have "?A \<subseteq> split_poly K -` ({z} \<times> M)"
    unfolding split_poly_def z_def M_def bounded_degree_polynomials_length
    by (rule subsetI, auto intro!:coeff_in_carrier coeff_length)
  moreover have "?A \<subseteq> carrier (poly_ring R)"
    unfolding bounded_degree_polynomials_length by blast
  ultimately have a:"?A \<subseteq> split_poly K -` ({z} \<times> M) \<inter> carrier (poly_ring R)"
    by blast

  have "\<And>x k . (\<lambda>k. coeff x (k + card K)) \<in> M \<Longrightarrow> k \<ge> n + card K \<Longrightarrow> coeff x k = \<zero>"
    by (simp add:M_def, metis Nat.le_diff_conv2 Nat.le_imp_diff_is_add add_leD2)
  hence "split_poly K -` ({z} \<times> M) \<inter> carrier (poly_ring R) \<subseteq> bounded_degree_polynomials R (card K + n)"
    unfolding split_poly_def z_def using poly_degree_bound_from_coeff_1 inv_subsetI by force
  moreover have "\<And>\<omega> k. \<omega> \<in> split_poly K -` ({z} \<times> M) \<inter> carrier (poly_ring R) \<Longrightarrow> k \<in> K \<Longrightarrow> eval \<omega> k = f k"
    unfolding split_poly_def z_def using restrict_eq_imp by fastforce
  ultimately have b:"split_poly K -` ({z} \<times> M) \<inter> carrier (poly_ring R) \<subseteq> ?A"
    by blast

  have "z \<in> K \<rightarrow>\<^sub>E carrier R"
    unfolding z_def using assms(3) by auto
  moreover have "M \<subseteq> {f. range f \<subseteq> carrier R \<and> (\<exists>n. (\<forall>k \<ge> n. f k = \<zero>))}"
    unfolding M_def by blast
  ultimately have c:"{z} \<times> M \<subseteq> split_poly K ` carrier (poly_ring R)"
    using split_poly_image[OF assms(1) assms(2)] by fast

  have "card ?A = card (split_poly K -` ({z} \<times> M) \<inter> carrier (poly_ring R))"
    using order_antisym[OF a b] by simp
  also have "... = card ({z} \<times> M)"
    using card_vimage_inj_on[OF inj_on_bounded] c by blast
  also have "... = card (carrier R)^n"
    by (simp add:card_cartesian_product M_def card_mostly_constant_maps)
  finally show ?thesis by simp
qed

text \<open>A corollary is the classic result~\<^cite>\<open>\<open>Theorem 7.15\<close> in "shoup2009computational"\<close> that there is
exactly one polynomial of degree less than $n$ interpolating $n$ points:\<close>

corollary (in field) interpolating_polynomial_one:
  assumes "finite K"
  assumes "K \<subseteq> carrier R"
  assumes "f ` K \<subseteq> carrier R"
  shows "card {\<omega> \<in> bounded_degree_polynomials R (card K). (\<forall>k \<in> K. eval \<omega> k = f k)} = 1"
  using interpolating_polynomials_card[OF assms(1) assms(2) assms(3), where n="0"]
  by simp

text \<open>In the case of fields with infinite carriers, it is possible to conclude that there are
infinitely many polynomials of degree less than $n$ interpolating $k < n$ points.\<close>

corollary (in field) interpolating_polynomial_inf:
  assumes "infinite (carrier R)"
  assumes "finite K" "K \<subseteq> carrier R" "f ` K \<subseteq> carrier R"
  assumes "n > 0"
  shows "infinite {\<omega> \<in> bounded_degree_polynomials R (card K + n). (\<forall>k \<in> K. eval \<omega> k = f k)}"
    (is "infinite ?A")
proof -
  have "{} \<subset> {\<omega> \<in> bounded_degree_polynomials R (card K). (\<forall>k \<in> K. eval \<omega> k = f k)}"
    using interpolating_polynomial_one[OF assms(2) assms(3) assms(4)] by fastforce
  also have "... \<subseteq> ?A"
    unfolding bounded_degree_polynomials_def by auto
  finally have a:"?A \<noteq> {}" by auto

  have "card ?A = card (carrier R)^n"
    using interpolating_polynomials_card[OF assms(2) assms(3) assms(4), where n="n"] by simp
  also have "... = 0"
    using assms(1) assms(5) by simp
  finally have b:"card ?A = 0" by simp

  show ?thesis using a b card_0_eq by blast
qed

text \<open>The following is an additional independent result: The evaluation homomorphism is injective
for degree one polynomials.\<close>

lemma  (in field) eval_inj_if_degree_1:
  assumes "p \<in> carrier (poly_ring R)" "degree p = 1"
  shows "inj_on (eval p) (carrier R)"
proof -
  obtain u v where p_def: "p = [u,v]" using assms
    by (cases p, cases "(tl p)", auto)

  have "u \<in> carrier R - {\<zero>}" using p_def assms by blast
  moreover have "v \<in> carrier R" using p_def assms by blast
  ultimately show ?thesis by (simp add:p_def field_Units inj_on_def)
qed

end
