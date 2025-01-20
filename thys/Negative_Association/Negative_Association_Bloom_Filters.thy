section \<open>Application: Bloom Filters\<close>

text \<open>The false positive probability of Bloom Filters is a case where negative association is
really useful. Traditionally it is derived only approximately. Bloom~\cite{bloom1970} first derives
the expected number of bits set to true given the number of elements inserted, then the false
positive probability is computed, pretending that the expected number of bits is the actual number
of bits.

Both Blooms original derivation and Mitzenmacher and Upfal~\cite{mitzenmacher2017} use this method.

A more correct approach would be to derive a tail bound for the number of set bits and derive
a false-positive probability based on that, which unfortunately leads to a complex formula.

An exact result has later been derived using combinatorial methods by Gopinathan and
Sergey~\cite{gopinathan2020}. However their formula is less useful, as it consists of a sum
with Stirling numbers and binomial coefficients.

It is however easy to see that the original bound derived by Bloom is a correct upper bound for the
false positive probability using negative association. (This is pointed out by
Bao et al.~\cite{bao2021}.)

In this section, we derive the same bound using this library as an example for the applicability of
this library.\<close>

theory Negative_Association_Bloom_Filters
  imports Negative_Association_Permutation_Distributions
begin

fun bloom_filter_pmf where
  "bloom_filter_pmf 0 d N = return_pmf {}" |
  "bloom_filter_pmf (Suc n) d N = do {
      h \<leftarrow> bloom_filter_pmf n d N;
      a \<leftarrow> pmf_of_set {a. a \<subseteq> {..<(N::nat)} \<and> card a = d};
      return_pmf (a \<union> h)
    }"

lemma bloom_filter_neg_assoc:
  assumes "d \<le> N"
  shows "measure_pmf.neg_assoc (bloom_filter_pmf n d N) (\<lambda>i \<omega>. i \<in> \<omega>) {..<N}"
proof (induction n)
  case 0

  have a:"measure_pmf.neg_assoc (bloom_filter_pmf 0 d N) (\<lambda>_ _. False) {..<N}"
    by (intro measure_pmf.indep_imp_neg_assoc measure_pmf.indep_vars_const) auto
  show ?case by (intro measure_pmf.neg_assoc_cong[OF _ _ a] AE_pmfI) simp_all
next
  case (Suc n)
  let ?l = "bloom_filter_pmf n d N"
  let ?r = "pmf_of_set {a. a \<subseteq> {..<N} \<and> card a = d}"

  define f where "f j \<omega> = (\<omega> (True,j) \<or> \<omega> (False,j))" for \<omega> and j :: nat

  have f_borel: "f i \<in> borel_measurable (Pi\<^sub>M (UNIV \<times> {i}) (\<lambda>_. borel))" (is "?L \<in> ?R") for i
  proof -
    have "f i = (\<lambda>\<omega>. max(fst \<omega>) (snd \<omega>)) \<circ> (\<lambda>\<omega>. (\<omega> (True,i),\<omega> (False,i)))" unfolding f_def by auto
    also have "\<dots> \<in> ?R" by (intro measurable_comp[where N="borel \<Otimes>\<^sub>M borel"]) measurable
    finally show ?thesis by simp
  qed

  have 0:"{True} \<times>{..<N} \<union> {False} \<times>{..<N} = UNIV\<times>{..<N}" by auto

  have s:"{b} \<times> {..<N} = Pair b ` {..<N}" for b :: bool by auto

  have "measure_pmf.neg_assoc (map_pmf snd (pair_pmf ?l ?r)) (\<lambda>i \<omega>. i \<in> \<omega>) ({..<N})"
    unfolding map_snd_pair_pmf using assms by (intro n_subsets_distribution_neg_assoc) auto
  hence na_l:
    "measure_pmf.neg_assoc (pair_pmf ?l ?r) (\<lambda>i \<omega>. snd i \<in> case_bool fst snd (fst i) \<omega>) ({False} \<times> {..<N})"
    unfolding s neg_assoc_map_pmf by (subst measure_pmf.neg_assoc_reindex) (auto intro:inj_onI)

  have "measure_pmf.neg_assoc (map_pmf fst (pair_pmf ?l ?r)) (\<in>) ({..<N})"
    unfolding map_fst_pair_pmf using Suc by simp
  hence na_r:
    "measure_pmf.neg_assoc (pair_pmf ?l ?r) (\<lambda>i \<omega>. snd i \<in> case_bool fst snd (fst i) \<omega>) ({True} \<times> {..<N})"
    unfolding s neg_assoc_map_pmf by (subst measure_pmf.neg_assoc_reindex) (auto intro:inj_onI)

  have c: "prob_space.indep_var (pair_pmf ?l ?r)
     (PiM ({True} \<times> {..<N}) (\<lambda>_. borel)) x (PiM ({False} \<times> {..<N}) (\<lambda>_. borel)) y"
    if "x = ((\<lambda>\<omega>. \<lambda>i\<in>{True} \<times> {..<N}. snd i\<in> \<omega>)\<circ>fst)" "y=((\<lambda>\<omega>. \<lambda>i\<in>{False} \<times> {..<N}. snd i \<in> \<omega>)\<circ>snd)"
    for x y
    unfolding that by (intro prob_space.indep_var_compose[OF _ indep_var_pair_pmf] prob_space_measure_pmf)
      (auto simp:space_PiM)

  have a:"measure_pmf.neg_assoc (pair_pmf ?l ?r) (\<lambda>i \<omega>. snd i \<in> case_bool fst snd (fst i) \<omega>) (UNIV \<times> {..<N})"
    by (intro measure_pmf.neg_assoc_combine[OF _ 0] na_l na_r c) (auto simp: restrict_def mem_Times_iff)
  have "measure_pmf.neg_assoc (pair_pmf ?l ?r) (\<lambda>i \<omega>. f i (\<lambda>i. snd i \<in> case_bool fst snd (fst i) \<omega>)) {..<N}"
    by (intro measure_pmf.neg_assoc_compose[OF _ a, where deps="\<lambda>j. UNIV\<times>{j}" and \<eta>="Fwd"]
        monotoneI depends_onI f_borel) (auto simp:f_def)
  hence "measure_pmf.neg_assoc (pair_pmf ?l ?r) (\<lambda>i \<omega>. i \<in> fst \<omega> \<or> i \<in> snd \<omega>) {..<N}"
    unfolding f_def by (simp add:case_prod_beta')
  hence "measure_pmf.neg_assoc (map_pmf (case_prod (\<union>)) (pair_pmf ?l ?r)) (\<in>) {..<N}"
    unfolding neg_assoc_map_pmf by (simp add:case_prod_beta')
  thus ?case by (simp add:pair_pmf_def map_bind_pmf Un_commute)
qed

lemma bloom_filter_cell_prob:
  assumes "d \<le> N" "i < N"
  shows "measure (bloom_filter_pmf n d N) {\<omega>. i \<in> \<omega>} = 1 - (1 - real d/real N)^n"
proof -
  have "measure (bloom_filter_pmf n d N) {\<omega>. i \<notin> \<omega>} = (1 - real d/real N)^n"
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    let ?p = "pair_pmf (bloom_filter_pmf n d N) (pmf_of_set {a. a \<subseteq> {..<N} \<and> card a = d})"

    have a:" {\<omega>. i \<notin> fst \<omega> \<and> i \<notin> snd \<omega>} = ({\<omega>. i \<notin> \<omega>}) \<times> ({\<omega>. i \<notin> \<omega>})" by auto

    have "measure ?p {\<omega>. i \<notin> fst \<omega> \<and> i \<notin> snd \<omega>} = (1-real d/N) ^ n *  (1-real d/card {..<N})"
      using assms unfolding a measure_pair_pmf
      by (intro Suc n_subsets_prob(1) arg_cong2[where f="(*)"]) auto
    also have "\<dots> =  (1-real d/N) ^ (n+1)" by simp
    finally have "measure ?p {\<omega>. i \<notin> fst \<omega> \<and> i \<notin> snd \<omega>} = (1-real d/N) ^ (n+1)" by simp

    hence "measure (map_pmf (\<lambda>\<omega>. snd \<omega> \<union> fst \<omega>) ?p) {\<omega>. i \<notin> \<omega>} =  (1-real d/N)^(n+1)"
      by (simp add:disj_commute)
    thus ?case by (simp add:pair_pmf_def map_bind_pmf)
  qed
  hence "1 - measure (bloom_filter_pmf n d N) {\<omega>. i \<in> \<omega>} = (1 - real d/real N)^n"
    by (subst measure_pmf.prob_compl[symmetric]) (auto simp:set_diff_eq)
  thus ?thesis by simp
qed

lemma bloom_filter_false_positive_prob:
  assumes "d \<le> N" "T \<subseteq> {..<N}" "card T = d"
  shows "measure (bloom_filter_pmf n d N) {\<omega>. T \<subseteq> \<omega>} \<le> (1 - (1 - real d/real N)^n)^d"
    (is "?L \<le> ?R")
proof -
  let ?p = "bloom_filter_pmf n d N"
  have na: "measure_pmf.neg_assoc (bloom_filter_pmf n d N) (\<lambda>i \<omega>. i \<in> \<omega>) T"
    by (intro measure_pmf.neg_assoc_subset[OF assms(2) bloom_filter_neg_assoc] assms(1))

  have fin_T: "finite T" using assms(2) finite_subset by auto
  hence a: "of_bool (T \<subseteq> y) = (\<Prod>t\<in>T. of_bool (t \<in> y)::real)" for y
    by (induction T) auto

  have "?L = measure ?p ({\<omega>. T \<subseteq> \<omega>} \<inter> space ?p)" by simp
  also have "\<dots> = (\<integral>\<omega>. (\<Prod>t \<in> T. of_bool(t \<in> \<omega>)) \<partial>?p)"
    unfolding Bochner_Integration.integral_indicator[symmetric] indicator_def
    using a by (intro integral_cong_AE AE_pmfI) auto
  also have "\<dots> \<le> (\<Prod>t \<in> T. (\<integral>\<omega>. of_bool(t \<in> \<omega>) \<partial>?p))"
    by (intro has_int_thatD(2)[OF measure_pmf.neg_assoc_imp_prod_mono[OF _ na, where \<eta>="Fwd"]]
        integrable_bounded_pmf bounded_range_imp[OF bounded_of_bool] fin_T
        borel_measurable_continuous_onI) (auto intro:monoI)
  also have "\<dots> = (\<Prod>t \<in> T. measure ?p ({\<omega>. t \<in> \<omega>} \<inter> space ?p))"
    unfolding Bochner_Integration.integral_indicator[symmetric] indicator_def by simp
  also have "\<dots> = (\<Prod>t \<in> T. measure ?p {\<omega>. t \<in> \<omega>})" by simp
  also have "\<dots> = (\<Prod>t \<in> T. 1 - (1 - real d/real N)^n)"
    using assms(1,2) by (intro prod.cong bloom_filter_cell_prob) auto
  also have "\<dots> = ?R" using assms(3) by simp
  finally show ?thesis by simp
qed

end