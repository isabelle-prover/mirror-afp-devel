section \<open>Carter-Wegman Hash Family\label{sec:carter_wegman}\<close>

theory Carter_Wegman_Hash_Family
  imports
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities
    Universal_Hash_Families_More_Independent_Families
begin

text \<open>The Carter-Wegman hash family is a generic method to obtain
$k$-universal hash families for arbitrary $k$. (There are faster solutions, such as tabulation
hashing, which are limited to a specific $k$. See for example \<^cite>\<open>"thorup2010"\<close>.)

The construction was described by Wegman and Carter~\<^cite>\<open>"wegman1981"\<close>, it is a hash
family between the elements of a finite field and works by choosing randomly a polynomial
over the field with degree less than $k$. The hash function is the evaluation of a such a
polynomial.

Using the property that the fraction of polynomials interpolating a given set of $s \leq k$
points is @{term "1/(card (carrier R)^s)"}, which is shown in
\<^cite>\<open>"Interpolation_Polynomials_HOL_Algebra-AFP"\<close>, it is possible to obtain both that
the hash functions are $k$-wise independent and uniformly distributed.

In the following two locales are introduced, the main reason for both is to make the statements
of the theorems and proofs more concise. The first locale @{term "poly_hash_family"} fixes a finite
ring $R$ and the probability space of the polynomials of degree less than $k$. Because the ring is
not a field, the family is not yet $k$-universal, but it is still possible to state a few results such
as the fact that the range of the hash function is a subset of the carrier of the ring.

The second locale @{term "carter_wegman_hash_family"} is an extension of the former with the
assumption that $R$ is a field with which the $k$-universality follows.

The reason for using two separate locales is to support use cases, where the ring is only probably
a field. For example if it is the set of integers modulo an approximate prime, in such a situation a
subset of the properties of an algorithm using approximate primes would need to be verified
even if $R$ is only a ring.\<close>

definition (in ring) "hash x \<omega> = eval \<omega> x"

locale poly_hash_family = ring +
  fixes k :: nat
  assumes finite_carrier[simp]: "finite (carrier R)"
  assumes k_ge_0: "k > 0"
begin

definition space where "space = bounded_degree_polynomials R k"
definition M where "M = measure_pmf (pmf_of_set space)"

lemma finite_space[simp]:"finite space"
    unfolding space_def using fin_degree_bounded finite_carrier by simp

lemma non_empty_bounded_degree_polynomials[simp]:"space \<noteq> {}"
    unfolding space_def using non_empty_bounded_degree_polynomials by simp

text \<open>This is to add @{thm [source] carrier_not_empty} to the simp set in the context of
@{locale "poly_hash_family"}:\<close>

lemma non_empty_carrier[simp]: "carrier R \<noteq> {}"
  by (simp add:carrier_not_empty)

sublocale prob_space "M"
  by (simp add:M_def prob_space_measure_pmf)

lemma hash_range[simp]:
  assumes "\<omega> \<in> space"
  assumes "x \<in> carrier R"
  shows "hash x \<omega> \<in> carrier R"
  using assms unfolding hash_def space_def bounded_degree_polynomials_def
  by (simp, metis eval_in_carrier polynomial_incl univ_poly_carrier)

lemma  hash_range_2:
  assumes "\<omega> \<in> space"
  shows "(\<lambda>x. hash x \<omega>) ` carrier R \<subseteq> carrier R"
  using hash_range assms by auto

lemma integrable_M[simp]:
  fixes f :: "'a list \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable M f"
    unfolding M_def
    by (rule integrable_measure_pmf_finite, simp)

end

locale carter_wegman_hash_family = poly_hash_family +
  assumes field_R: "field R"
begin
sublocale field
  using field_R by simp

abbreviation "field_size \<equiv> card (carrier R)"

lemma poly_cards:
  assumes "K \<subseteq> carrier R"
  assumes "card K \<le> k"
  assumes "y ` K \<subseteq> (carrier R)"
  shows
    "card {\<omega> \<in> space. (\<forall>k \<in> K. eval \<omega> k = y k)} = field_size^(k-card K)"
  unfolding space_def
  using interpolating_polynomials_card[where n="k-card K" and K="K"] assms
  using finite_carrier finite_subset by fastforce

lemma poly_cards_single:
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  shows "card {\<omega> \<in> space. eval \<omega> x = y} = field_size^(k-1)"
  using poly_cards[where K="{x}" and y="\<lambda>_. y", simplified] assms k_ge_0 by simp

lemma hash_prob:
  assumes "K \<subseteq> carrier R"
  assumes "card K \<le> k"
  assumes "y ` K \<subseteq> carrier R"
  shows
    "prob {\<omega>. (\<forall>x \<in> K. hash x \<omega> = y x)} = 1/(real field_size)^card K"
proof -
  have "\<zero> \<in> carrier R" by simp

  hence a:"field_size > 0"
    using finite_carrier card_gt_0_iff by blast

  have b:"real (card {\<omega> \<in> space. \<forall>x\<in>K. eval \<omega> x = y x}) / real (card space) =
    1 / real field_size ^ card K"
    using a assms(2)
    apply (simp add: frac_eq_eq poly_cards[OF assms(1,2,3)] power_add[symmetric])
    by (simp add:space_def bounded_degree_polynomials_card)

  show ?thesis
    unfolding M_def
    by (simp add:hash_def measure_pmf_of_set Int_def b)
qed

lemma prob_single:
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "prob {\<omega>. hash x \<omega> = y} = 1/(real field_size)"
  using hash_prob[where K="{x}"] assms finite_carrier k_ge_0 by simp

lemma prob_range:
  assumes [simp]:"x \<in> carrier R"
  shows "prob {\<omega>. hash x \<omega> \<in> A} = card (A \<inter> carrier R) / field_size"
proof -
  have "prob {\<omega>. hash x \<omega> \<in> A} = prob (\<Union>a \<in> A \<inter> carrier R. {\<omega>. hash x \<omega> = a})"
    by (rule measure_pmf_eq, auto simp:M_def)
  also have "... = (\<Sum> a \<in> (A \<inter> carrier R). prob {\<omega>. hash x \<omega> = a})"
    by (rule measure_finite_Union, auto simp:M_def disjoint_family_on_def)
  also have "... = (\<Sum> a \<in> (A \<inter> carrier R). 1/(real field_size))"
    by (rule sum.cong, auto simp:prob_single)
  also have "... = card (A \<inter> carrier R) / field_size"
    by simp
  finally show ?thesis by simp
qed

lemma indep:
  assumes "J \<subseteq> carrier R"
  assumes "card J \<le> k"
  shows "indep_vars (\<lambda>_. discrete) hash J"
proof -
  have "\<zero> \<in> carrier R" by simp
  hence card_R_ge_0:"field_size > 0"
    using card_gt_0_iff finite_carrier by blast

  have fin_J: "finite J"
    using finite_carrier assms(1) finite_subset by blast

  show ?thesis
  proof (rule indep_vars_pmf[OF M_def])
    fix a
    fix J'
    assume a: "J' \<subseteq> J" "finite J'"
    have card_J': "card J' \<le> k"
      by (metis card_mono order_trans a(1) assms(2) fin_J)
    have J'_in_carr: "J' \<subseteq> carrier R" by (metis order_trans a(1) assms(1))

    show "prob {\<omega>. \<forall>x\<in>J'. hash x \<omega> = a x} = (\<Prod>x\<in>J'. prob  {\<omega>. hash x \<omega> = a x})"
    proof (cases "a ` J' \<subseteq> carrier R")
      case True
      have a_carr: "\<And>x. x \<in> J' \<Longrightarrow> a x \<in> carrier R"  using True by force
      have "prob {\<omega>. \<forall>x\<in>J'. hash x \<omega> = a x} =
        real (card {\<omega> \<in> space. \<forall>x\<in>J'. eval \<omega> x = a x}) / real (card space)"
        by (simp add:M_def measure_pmf_of_set Int_def hash_def)
      also have "... = real (field_size ^ (k - card J')) / real (card space)"
        using True by (simp add: poly_cards[OF J'_in_carr card_J'])
      also have
        "... = real field_size ^ (k - card J') / real field_size ^ k"
        by (simp add:space_def bounded_degree_polynomials_card)
      also have
        "... = real field_size ^ ((k - 1) * card J') / real field_size ^ (k * card J')"
        using card_J' by (simp add:power_add[symmetric] power_mult[symmetric]
            diff_mult_distrib frac_eq_eq add.commute)
      also have
        "... = (real field_size ^ (k - 1)) ^ card J' / (real field_size ^ k) ^ card J'"
        by (simp add:power_add power_mult)
      also have
        "... =  (\<Prod>x\<in>J'. real (card {\<omega> \<in> space. eval \<omega> x = a x}) / real (card space))"
        using a_carr poly_cards_single[OF subsetD[OF J'_in_carr]]
        by (simp add:space_def bounded_degree_polynomials_card power_divide)
      also have "... = (\<Prod>x\<in>J'. prob {\<omega>. hash x \<omega> = a x})"
        by (simp add:measure_pmf_of_set M_def Int_def hash_def)
      finally show ?thesis by simp
    next
      case False
      then obtain j where j_def: "j \<in> J'" "a j \<notin> carrier R" by blast
      have "{\<omega> \<in> space. hash j \<omega> = a j} \<subseteq> {\<omega> \<in> space. hash j \<omega> \<notin> carrier R}"
        by (rule subsetI, simp add:j_def)
      also have "... \<subseteq> {}" using j_def(1) J'_in_carr hash_range by blast
      finally have b:"{\<omega> \<in> space. hash j \<omega> = a j} = {}" by simp
      hence "real (card ({\<omega> \<in> space. hash j \<omega> = a j})) = 0" by simp
      hence "(\<Prod>x\<in>J'. real (card {\<omega> \<in> space. hash x \<omega> = a x})) = 0"
        using a(2) prod_zero[OF a(2)] j_def(1) by auto
      moreover have
        "{\<omega> \<in> space. \<forall>x\<in>J'. hash x \<omega> = a x} \<subseteq> {\<omega> \<in> space. hash j \<omega> = a j}"
        using j_def by blast
      hence "{\<omega> \<in> space. \<forall>x\<in>J'. hash x \<omega> = a x} = {}" using b by blast
      ultimately show ?thesis
        by (simp add:measure_pmf_of_set M_def Int_def prod_dividef)
    qed
  qed
qed

lemma k_wise_indep:
  "k_wise_indep_vars k (\<lambda>_. discrete) hash (carrier R)"
  unfolding k_wise_indep_vars_def using indep by simp

lemma inj_if_degree_1:
  assumes "\<omega> \<in> space"
  assumes "degree \<omega> = 1"
  shows "inj_on (\<lambda>x. hash x \<omega>) (carrier R)"
  using assms eval_inj_if_degree_1
  by (simp add:M_def space_def bounded_degree_polynomials_def hash_def)

lemma uniform:
  assumes "i \<in> carrier R"
  shows "uniform_on (hash i) (carrier R)"
proof -
  have a:
    "\<And>a. prob {\<omega>. hash i \<omega> \<in> {a}} = indicat_real (carrier R) a / real field_size"
    by (subst prob_range[OF assms], simp add:indicator_def)
  show ?thesis
    by (rule uniform_onI, use a M_def in auto)
qed

text \<open>This the main result of this section - the Carter-Wegman hash family is $k$-universal.\<close>

theorem k_universal:
  "k_universal k hash (carrier R) (carrier R)"
  using uniform k_wise_indep by (simp add:k_universal_def)

end

lemma poly_hash_familyI:
  assumes "ring R"
  assumes "finite (carrier R)"
  assumes "0 < k"
  shows "poly_hash_family R k"
  using assms
  by (simp add:poly_hash_family_def poly_hash_family_axioms_def)

lemma carter_wegman_hash_familyI:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "0 < k"
  shows "carter_wegman_hash_family F k"
  using assms field.is_ring[OF assms(1)] poly_hash_familyI
  by (simp add:carter_wegman_hash_family_def carter_wegman_hash_family_axioms_def)

lemma hash_k_wise_indep:
  assumes "field F \<and> finite (carrier F)"
  assumes "1 \<le> n"
  shows
    "prob_space.k_wise_indep_vars (pmf_of_set (bounded_degree_polynomials F n)) n
    (\<lambda>_. pmf_of_set (carrier F)) (ring.hash F) (carrier F)"
proof -
  interpret carter_wegman_hash_family "F" "n"
    using assms carter_wegman_hash_familyI by force
  have "k_wise_indep_vars n (\<lambda>_. pmf_of_set (carrier F)) hash (carrier F)"
    by (rule k_wise_indep_vars_compose[OF k_wise_indep], simp)
  thus ?thesis
    by (simp add:M_def space_def)
qed

lemma hash_prob_single:
  assumes "field F \<and> finite (carrier F)"
  assumes "x \<in> carrier F"
  assumes "1 \<le> n"
  assumes "y \<in> carrier F"
  shows
    "\<P>(\<omega> in pmf_of_set (bounded_degree_polynomials F n). ring.hash F x \<omega> = y)
      = 1/(real (card (carrier F)))"
proof -
  interpret carter_wegman_hash_family "F" "n"
    using assms carter_wegman_hash_familyI by force
  show ?thesis
    using prob_single[OF assms(2,4)] by (simp add:M_def space_def)
qed

end
