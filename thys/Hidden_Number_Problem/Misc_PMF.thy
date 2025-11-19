theory Misc_PMF
  imports
    "HOL-Probability.Probability"
    "LLL_Basis_Reduction.LLL_Impl"

begin

(* Copied from CRYSTALS-Kyber_Security *)
definition replicate_spmf :: "nat \<Rightarrow> 'b pmf \<Rightarrow> 'b list spmf" where
  "replicate_spmf m p = spmf_of_pmf (replicate_pmf m p)"

text "The preceding @{const replicate_spmf} definition is copied from \<open>CRYSTALS-Kyber_Security\<close>.
We do this to avoid loading the entire library.
In fact, we do not need @{const replicate_spmf} at all for the HNP.
However, for each @{const replicate_pmf} result we prove here,
we also prove a corresponding @{const replicate_spmf} result.
The @{const replicate_spmf} results are here for completeness,
but not needed for the HNP."

section "SPMF and PMF helper lemmas"

lemma spmf_eq_element: "spmf (p \<bind> (\<lambda>x. return_spmf (x = t))) True = spmf p t"
proof-
  have *: "map_option (\<lambda>a. a = t) -` {Some True} = {Some t}" by fastforce
  have "(p \<bind> (\<lambda>x. return_spmf (x = t))) = map_spmf (\<lambda>a. a = t) p"
    by (simp add: map_spmf_conv_bind_spmf)
  also have "spmf ... True = spmf p t" by (simp add: pmf_def *)
  finally show ?thesis .
qed

lemma pmf_true_false:
  fixes p :: "'a pmf"
  fixes P Q :: "'a \<Rightarrow> bool"
  defines "a \<equiv> p \<bind> (\<lambda>x. return_pmf (P x))"
  defines "b \<equiv> p \<bind> (\<lambda>x. return_pmf (\<not> P x))"
  shows "pmf a True = pmf b False"
proof-
  have "a = map_pmf P p" by (simp add: a_def map_pmf_def)
  moreover have "b = map_pmf (\<lambda>x. \<not> P x) p" by (simp add: b_def map_pmf_def)
  moreover have "P -` {True} = (\<lambda>x. \<not> P x) -` {False}" by blast
  ultimately show ?thesis by (simp add: pmf_def)
qed

lemma spmf_true_false:
  fixes p :: "'a spmf"
  fixes P Q :: "'a \<Rightarrow> bool"
  defines "a \<equiv> p \<bind> (\<lambda>x. return_spmf (P x))"
  defines "b \<equiv> p \<bind> (\<lambda>x. return_spmf (\<not> P x))"
  shows "spmf a True = spmf b False"
proof-
  have "a = map_spmf P p" by (simp add: a_def map_spmf_conv_bind_spmf)
  moreover have "b = map_spmf (\<lambda>x. \<not> P x) p" by (simp add: b_def map_spmf_conv_bind_spmf)
  moreover have "map_option P -` {Some True} = map_option (\<lambda>x. \<not> P x) -` {Some False}" by blast
  ultimately show ?thesis by (simp add: pmf_def)
qed

lemma pmf_subset:
  fixes p :: "'a pmf"
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes "\<forall>x \<in> set_pmf p. P x \<longrightarrow> Q x"
  shows "pmf (p \<bind> (\<lambda>x. return_pmf (P x))) True \<le> pmf (p \<bind> (\<lambda>x. return_pmf (Q x))) True"
proof-
  have "p \<bind> (\<lambda>x. return_pmf (P x)) = map_pmf P p" by (simp add: map_pmf_def)
  moreover have "p \<bind> (\<lambda>x. return_pmf (Q x)) = map_pmf Q p" by (simp add: map_pmf_def)
  moreover have "pmf (map_pmf P p) True \<le> pmf (map_pmf Q p) True"
  proof-
    have "pmf (map_pmf P p) True = prob_space.prob p ((P -` {True}) \<inter> set_pmf p)"
        (is "_ = prob_space.prob p ?lhs")
      by (simp add: measure_Int_set_pmf pmf_def)
    moreover have "pmf (map_pmf Q p) True = prob_space.prob p ((Q -` {True}) \<inter> set_pmf p)"
        (is "_ = prob_space.prob p ?rhs")
      by (simp add: measure_Int_set_pmf pmf_def)
    moreover have "?lhs \<subseteq> ?rhs" using assms in_set_spmf by fast
    ultimately show ?thesis by (simp add: measure_pmf.finite_measure_mono)
  qed
  ultimately show ?thesis by presburger
qed

lemma pmf_subset':
  fixes p :: "'a pmf"
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes "\<forall>x \<in> set_pmf p. \<not> P x \<longrightarrow> \<not> Q x"
  shows "pmf (p \<bind> (\<lambda>x. return_pmf (P x))) False \<le> pmf (p \<bind> (\<lambda>x. return_pmf (Q x))) False"
  using pmf_subset[OF assms(1)] pmf_true_false[of p "\<lambda>x. \<not> P x"] pmf_true_false[of p "\<lambda>x. \<not> Q x"]
  by algebra

lemma spmf_subset:
  fixes p :: "'a spmf"
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes "\<forall>x \<in> set_spmf p. P x \<longrightarrow> Q x"
  shows "spmf (p \<bind> (\<lambda>x. return_spmf (P x))) True \<le> spmf (p \<bind> (\<lambda>x. return_spmf (Q x))) True"
proof-
  have "p \<bind> (\<lambda>x. return_spmf (P x)) = map_spmf P p" by (simp add: map_spmf_conv_bind_spmf)
  moreover have "p \<bind> (\<lambda>x. return_spmf (Q x)) = map_spmf Q p" by (simp add: map_spmf_conv_bind_spmf)
  moreover have "spmf (map_spmf P p) True \<le> spmf (map_spmf Q p) True"
  proof-
    have "spmf (map_spmf P p) True = prob_space.prob p ((map_option P -` {Some True}) \<inter> set_pmf p)"
        (is "_ = prob_space.prob p ?lhs")
      by (simp add: measure_Int_set_pmf pmf_def)
    moreover have "spmf (map_spmf Q p) True = prob_space.prob p ((map_option Q -` {Some True}) \<inter> set_pmf p)"
        (is "_ = prob_space.prob p ?rhs")
      by (simp add: measure_Int_set_pmf pmf_def)
    moreover have "?lhs \<subseteq> ?rhs" using assms in_set_spmf by fast
    ultimately show ?thesis by (simp add: measure_pmf.finite_measure_mono)
  qed
  ultimately show ?thesis by presburger
qed

lemma spmf_subset':
  fixes p :: "'a spmf"
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes "\<forall>x \<in> set_spmf p. \<not> P x \<longrightarrow> \<not> Q x"
  shows "spmf (p \<bind> (\<lambda>x. return_spmf (P x))) False \<le> spmf (p \<bind> (\<lambda>x. return_spmf (Q x))) False"
  using spmf_subset[OF assms(1)] spmf_true_false[of p "\<lambda>x. \<not> P x"] spmf_true_false[of p "\<lambda>x. \<not> Q x"]
  by algebra

lemma pmf_in_set:
  fixes A :: "'a set"
  fixes p :: "'a pmf"
  shows "pmf (p \<bind> (\<lambda>x. return_pmf (x \<in> A))) True = prob_space.prob p A"
proof-
  have "p \<bind> (\<lambda>x. return_pmf (x \<in> A)) = map_pmf (\<lambda>x. x \<in> A) p" by (simp add: map_pmf_def)
  also have "pmf ... True = prob_space.prob p A"
  proof-
    have "(\<lambda>x. x \<in> A) -` {True} = A" by blast
    thus ?thesis by (simp add: pmf_def)
  qed
  finally show ?thesis .
qed

lemma pmf_of_prop:
  fixes P :: "'a \<Rightarrow> bool"
  fixes p :: "'a pmf"
  shows "pmf (p \<bind> (\<lambda>x. return_pmf (P x))) True = prob_space.prob p {x \<in> set_pmf p. P x}"
  using pmf_in_set[of p "{x \<in> set_pmf p. P x}"]
  by (smt (verit, best) bind_pmf_cong mem_Collect_eq)

lemma spmf_in_set:
  fixes A :: "'a set"
  fixes p :: "'a spmf"
  shows "spmf (p \<bind> (\<lambda>x. return_spmf (x \<in> A))) True = prob_space.prob p (Some`A)"
proof-
  have "p \<bind> (\<lambda>x. return_spmf (x \<in> A)) = map_spmf (\<lambda>x. x \<in> A) p"
    by (simp add: map_spmf_conv_bind_spmf)
  also have "spmf ... True = prob_space.prob p (Some`A)"
  proof-
    have "map_option (\<lambda>x. x \<in> A) -` {Some True} = Some`A" by blast
    thus ?thesis by (simp add: pmf_def)
  qed
  finally show ?thesis .
qed

lemma spmf_of_prop:
  fixes P :: "'a \<Rightarrow> bool"
  fixes p :: "'a spmf"
  shows "spmf (p \<bind> (\<lambda>x. return_spmf (P x))) True = prob_space.prob p (Some`{x \<in> set_spmf p. P x})"
  using spmf_in_set[of p "{x \<in> set_spmf p. P x}"]
  by (smt (verit) bind_spmf_cong mem_Collect_eq)

lemma replicate_pmf_events_helper:
  fixes p :: "'a pmf"
  fixes n P
  defines "lhs \<equiv> pmf (pair_pmf p (replicate_pmf n p) \<bind> (\<lambda>(x, xs). return_pmf (x # xs)) \<bind> (\<lambda>xs. return_pmf (P xs))) True"
  defines "rhs \<equiv> pmf (pair_pmf p (replicate_pmf n p) \<bind> (\<lambda>(x, xs). return_pmf (P (x # xs)))) True"
  shows "lhs = rhs"
  unfolding lhs_def rhs_def pmf_def apply simp
  by (smt (verit, ccfv_SIG) bind_assoc_pmf bind_pmf_cong bind_return_pmf case_prod_beta')

lemma replicate_pmf_events:
  fixes p :: "'a pmf"
  fixes n :: nat
  fixes E :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<forall>i < n. pmf (p \<bind> (\<lambda>x. return_pmf (E i x))) True = A i"
  shows "pmf (replicate_pmf n p \<bind> (\<lambda>xs. return_pmf (\<forall>i < n. E i (xs!i)))) True = (\<Prod>i<n. A i)"
  using assms
proof(induct n arbitrary: E A)
  case 0
  thus ?case by simp
next
  case (Suc n)
  define ps where "ps \<equiv> replicate_pmf (Suc n) p"
  define ps' where "ps' \<equiv> replicate_pmf n p"
  define E' where "E' \<equiv> \<lambda>n. E (Suc n)"
  define A' where "A' \<equiv> (\<lambda>i. pmf (p \<bind> (\<lambda>x. return_pmf (E' i x))) True)"
  have unfold: "replicate_pmf (Suc n) p = do {x \<leftarrow> p; xs \<leftarrow> replicate_pmf n p; return_pmf (x#xs)}"
    unfolding replicate_pmf_def by force

  let ?rpmf0 = "do {x \<leftarrow> p; xs \<leftarrow> ps'; return_pmf (x#xs)}"
  let ?rpmf0' = "do {(x, xs) \<leftarrow> pair_pmf p ps'; return_pmf (x#xs)}"
  let ?rpmf1' = "pair_pmf p ps'"
  have 0: "?rpmf0 = ?rpmf0'"
    by (smt (verit, best) bind_assoc_pmf bind_pmf_cong bind_return_pmf internal_case_prod_conv internal_case_prod_def pair_pmf_def)
  have *: "\<forall>xs \<in> set_pmf ?rpmf0. 
    (\<forall>i < Suc n. E i (xs!i)) \<longleftrightarrow> (E 0 (hd xs) \<and> (\<forall>i < n. E' i ((tl xs)!i)))"
  proof
    fix xs assume "xs \<in> set_pmf ?rpmf0"
    hence len: "length xs = Suc n" unfolding ps'_def using set_replicate_pmf by fastforce
    show "(\<forall>i < Suc n. E i (xs ! i)) \<longleftrightarrow> (E 0 (hd xs) \<and> (\<forall>i<n. E' i (tl xs ! i)))"
    proof 
      assume *: "\<forall>i < Suc n. E i (xs ! i)"
      hence "E 0 (hd xs)"
        by (metis len Nat.nat.distinct(1) hd_conv_nth length_0_conv zero_less_Suc)
      moreover have "(\<forall>i<n. E' i (tl xs ! i))"
      proof safe
        fix i assume **: "i < n"
        hence "Suc i < Suc n" by blast
        hence "E (Suc i) (xs ! (Suc i))" using * by presburger
        thus "E' i (tl xs ! i)" unfolding E'_def by (simp add: ** nth_tl len)
      qed
      ultimately show "E 0 (hd xs) \<and> (\<forall>i<n. E' i (tl xs ! i))" by blast
    next
      assume *: "E 0 (hd xs) \<and> (\<forall>i<n. E' i (tl xs ! i))"
      show "\<forall>i < Suc n. E i (xs ! i)"
      proof safe
        fix i assume **: "i < Suc n"
        show "E i (xs ! i)"
        proof(cases "i = 0")
          case True
          then show ?thesis by (metis "*" Nat.nat.distinct(1) hd_conv_nth len length_0_conv)
        next
          case False
          hence "E' (i - 1) = E i" unfolding E'_def by simp
          moreover have "i - 1 < n" using ** False by linarith
          ultimately show ?thesis
            by (metis "*" "**" False diff_Suc_1 len length_tl less_Suc_eq_0_disj nth_tl)
        qed
      qed
    qed
  qed

  have "pmf (ps \<bind> (\<lambda>xs. return_pmf (\<forall>i < Suc n. E i (xs!i)))) True
      = pmf (?rpmf0 \<bind> (\<lambda>xs. return_pmf (\<forall>i < Suc n. E i (xs!i)))) True"
    by (simp add: replicate_spmf_def ps_def ps'_def)
  also have "... = pmf (?rpmf0 \<bind> (\<lambda>xs. return_pmf (E 0 (hd xs) \<and> (\<forall>i < n. E' i ((tl xs)!i))))) True"
    unfolding pmf_def by (smt (verit, ccfv_SIG) "*" bind_pmf_cong)
  also have "... = pmf (?rpmf0' \<bind> (\<lambda>xs. return_pmf (E 0 (hd xs) \<and> (\<forall>i < n. E' i ((tl xs)!i))))) True"
    using 0 by presburger
  also have "... = pmf (?rpmf1' \<bind> (\<lambda>(x,xs). return_pmf (E 0 (hd (x#xs)) \<and> (\<forall>i < n. E' i ((tl (x#xs))!i))))) True"
    using replicate_pmf_events_helper[of p n "\<lambda>xs. (E 0 (hd xs) \<and> (\<forall>i < n. E' i ((tl xs)!i)))", folded ps'_def] .
  also have "... = pmf (?rpmf1' \<bind> (\<lambda>(x,xs). return_pmf (E 0 x \<and> (\<forall>i < n. E' i (xs!i))))) True"
    by simp
  also have "... = pmf (?rpmf1' \<bind> (\<lambda>x. return_pmf (E 0 (fst x) \<and> (\<forall>i<n. E' i (snd x ! i))))) True"
  proof-
    have "(\<lambda>(x, xs). return_pmf (E 0 x \<and> (\<forall>i<n. E' i (xs ! i)))) = (\<lambda>x. return_pmf (E 0 (fst x) \<and> (\<forall>i<n. E' i (snd x ! i))))"
      by force
    thus ?thesis by presburger
  qed
  also have "... = (measure (measure_pmf ?rpmf1')
      {x \<in> set_pmf ?rpmf1'. E 0 (fst x) \<and> (\<forall>i<n. E' i (snd x ! i))})"
    using pmf_of_prop[of ?rpmf1' "\<lambda>x_xs. E 0 (fst x_xs) \<and> (\<forall>i<n. E' i ((snd x_xs) ! i))"] .
  also have "... = measure (measure_pmf ?rpmf1')
      {(x,xs) \<in> set_pmf ?rpmf1'. E 0 x \<and> (\<forall>i < n. E' i (xs!i))}"
  proof-
    have "{x \<in> set_pmf ?rpmf1'. E 0 (fst x) \<and> (\<forall>i<n. E' i (snd x ! i))}
        \<subseteq> {(x,xs) \<in> set_pmf ?rpmf1'. E 0 x \<and> (\<forall>i < n. E' i (xs!i))}"
      by force
    moreover have "{(x,xs) \<in> set_pmf ?rpmf1'. E 0 x \<and> (\<forall>i < n. E' i (xs!i))}
        \<subseteq> {x \<in> set_pmf ?rpmf1'. E 0 (fst x) \<and> (\<forall>i<n. E' i (snd x ! i))}"
      by force
    ultimately show ?thesis by force
  qed
  also have "... = measure (measure_pmf p) {x \<in> set_pmf p. E 0 x}
      * measure (measure_pmf ps') {xs \<in> set_pmf ps'. \<forall>i < n. E' i (xs!i)}"
  proof-
    let ?A = "{x \<in> set_pmf p. E 0 x}"
    let ?B = "{xs \<in> set_pmf ps'. \<forall>i < n. E' i (xs!i)}"
    have 1: "countable ?A" by simp
    have 2: "countable ?B" by simp
    have "{(x,xs) \<in> set_pmf ?rpmf1'. E 0 x \<and> (\<forall>i < n. E' i (xs!i))} = ?A \<times> ?B" by force
    thus ?thesis using measure_pmf_prob_product[OF 1 2, of p ps'] by presburger
  qed
  also have "... = A 0 * (\<Prod>i<n. A' i)"
  proof-
    have 1: "\<forall>i<n. pmf (p \<bind> (\<lambda>x. return_pmf (E' i x))) True = A' i"
      unfolding A'_def by blast
    have "measure (measure_pmf p) {x \<in> set_pmf p. E 0 x} = A 0"
      using Suc.prems pmf_of_prop[of p "E 0"] by force
    moreover have "measure (measure_pmf ps') {xs \<in> set_pmf ps'. \<forall>i < n. E' i (xs!i)} = (\<Prod>i < n. A' i)"
      using Suc.hyps[OF 1, folded ps'_def]
      using pmf_of_prop[of "replicate_pmf n p" "\<lambda>xs. (\<forall>i < n. E' i (xs ! i))", folded ps'_def]
      by presburger
    ultimately show ?thesis by presburger
  qed
  also have "... = A 0 * (\<Prod>i=1..<Suc n. A i)"
  proof-
    have "(\<Prod>i=1..<Suc n. A i) = (\<Prod>i=1..<Suc n. A' (i - 1))" 
      unfolding A'_def E'_def using Suc.prems by force
    also have "... = (\<Prod>i=0..<n. A' i)"
      by (metis (mono_tags, lifting) Groups_Big.comm_monoid_mult_class.prod.cong Set_Interval.comm_monoid_mult_class.prod.atLeast_Suc_lessThan_Suc_shift diff_Suc_1 numeral_nat(7) o_apply)
    finally show ?thesis using atLeast0LessThan by presburger
  qed
  also have "... = (\<Prod>i<Suc n. A i)"
    by (simp add: prod.atLeast1_atMost_eq prod.atMost_shift atLeastLessThanSuc_atLeastAtMost lessThan_Suc_atMost)
  finally show ?case unfolding ps_def by auto
qed

lemma replicate_pmf_same_event:
  fixes p :: "'a pmf"
  fixes n :: nat
  fixes E :: "'a \<Rightarrow> bool"
  assumes "pmf (p \<bind> (\<lambda>x. return_pmf (E x))) True = A"
  shows "pmf (replicate_pmf n p \<bind> (\<lambda>xs. return_pmf (\<forall>i < n. E (xs!i)))) True = A^n"
  using replicate_pmf_events[of n p "\<lambda>i::nat. E" "\<lambda>i::nat. A"] assms by force

lemma replicate_pmf_same_event_leq:
  fixes p :: "'a pmf"
  fixes n :: nat
  fixes E :: "'a \<Rightarrow> bool"
  assumes "pmf (p \<bind> (\<lambda>x. return_pmf (E x))) True \<le> A"
  shows "pmf (replicate_pmf n p \<bind> (\<lambda>xs. return_pmf (\<forall>i < n. E (xs!i)))) True \<le> A^n"
  by (metis replicate_pmf_same_event assms pmf_nonneg pow_mono)

lemma replicate_spmf_events:
  fixes p :: "'a spmf"
  fixes n :: nat
  fixes E :: "nat \<Rightarrow> 'a option \<Rightarrow> bool"
  assumes "\<forall>i < n. (spmf (p \<bind> (\<lambda>x. return_spmf (E i x))) True = A i)"
  shows "spmf (replicate_spmf n p \<bind> (\<lambda>xs. return_spmf (\<forall>i < n. E i (xs!i)))) True = (\<Prod>i<n. A i)"
proof-
  have *: "\<forall>i < n. pmf (p \<bind> (\<lambda>x. return_pmf (E i x))) True
      = spmf (p \<bind> (\<lambda>x. return_spmf (E i x))) True"
    by (metis (no_types, lifting) bind_pmf_cong spmf_of_pmf_bind spmf_of_pmf_return_pmf spmf_spmf_of_pmf)
  have "spmf (replicate_spmf n p \<bind> (\<lambda>xs. return_spmf (\<forall>i < n. E i (xs!i)))) True
      = pmf (replicate_pmf n p \<bind> (\<lambda>xs. return_pmf (\<forall>i < n. E i (xs!i)))) True"
    by (metis (no_types, lifting) bind_spmf_cong bind_spmf_of_pmf replicate_spmf_def spmf_of_pmf_bind spmf_of_pmf_return_pmf spmf_spmf_of_pmf)
  also have "... = (\<Prod>i<n. A i)"
    using replicate_pmf_events[OF *] assms(1) by force
  finally show ?thesis .
qed

lemma replicate_spmf_same_event:
  fixes p :: "'a spmf"
  fixes n :: nat
  fixes E :: "'a option \<Rightarrow> bool"
  assumes "spmf (p \<bind> (\<lambda>x. return_spmf (E x))) True = A"
  shows "spmf (replicate_spmf n p \<bind> (\<lambda>xs. return_spmf (\<forall>i < n. E (xs!i)))) True = A^n"
  using replicate_spmf_events[of n p "\<lambda>i::nat. E" "\<lambda>i::nat. A"] assms by force

lemma replicate_pmf_indep':
  fixes p :: "'a pmf"
  fixes n :: nat
  fixes E :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  defines "rp \<equiv> replicate_pmf n p"
  assumes "\<forall>i < n. pmf (p \<bind> (\<lambda>x. return_pmf (E i x))) True = A i"
  assumes "I \<subseteq> {..<n}"
  assumes "\<forall>i < n. i \<notin> I \<longrightarrow> A i = 1"
  shows "pmf (replicate_pmf n p \<bind> (\<lambda>xs. return_pmf (\<forall>i < n. E i (xs!i)))) True = (\<Prod>i\<in>I. A i)"
proof-
  have "(\<Prod>i<n. A i) = (\<Prod>i\<in>I. A i)"
  proof-
    have "(\<Prod>i<n. A i) = (\<Prod>i\<in>{..<n}. A i)" by blast
    moreover have "... = (\<Prod>i\<in>{..<n}-I. A i) * (\<Prod>i\<in>I \<inter> {..<n}. A i)"
      by (simp add: Groups_Big.comm_monoid_mult_class.prod.subset_diff Int_absorb2 assms(3))
    moreover have "... = (\<Prod>i\<in>{..<n}-I. 1) * (\<Prod>i\<in>I \<inter> {..<n}. A i)" using assms(4) by simp
    moreover have "... = (\<Prod>i\<in>I. A i)"
    proof-
      have "(\<Prod>i\<in>{..<n}-I. 1) = 1"
        using Groups_Big.comm_monoid_mult_class.prod.neutral_const by blast
      moreover have "I \<inter> {..<n} = I" using assms(3) by blast
      ultimately show ?thesis by force
    qed
    ultimately show "(\<Prod>i<n. A i) = (\<Prod>i\<in>I. A i)" by presburger
  qed
  thus ?thesis using replicate_pmf_events[OF assms(2)] by presburger
qed

lemma replicate_pmf_indep'':
  fixes p :: "'a pmf"
  fixes n :: nat
  fixes E :: "'a \<Rightarrow> bool"
  fixes i :: nat
  defines "rp \<equiv> replicate_pmf n p"
  defines "A \<equiv> pmf (p \<bind> (\<lambda>x. return_pmf (E x))) True"
  assumes "i < n"
  shows "pmf (replicate_pmf n p \<bind> (\<lambda>xs. return_pmf (E (xs!i)))) True = A"
proof-
  let ?I = "{i}"
  let ?E = "\<lambda>j x. if j = i then E x else True"
  let ?A = "\<lambda>j. if j = i then A else 1"

  have 1: "\<forall>i < n. (pmf (p \<bind> (\<lambda>x. return_pmf (?E i x))) True = ?A i)" using assms(2) by simp
  have 2: "?I \<subseteq> {..<n}" using assms(3) by blast
  have 3: "\<forall>i < n. i \<notin> ?I \<longrightarrow> ?A i = 1" by auto
  have *: "(\<lambda>xs. return_pmf (E (xs ! i)))
      = (\<lambda>xs. return_pmf (\<forall>j<n. if j = i then E (xs ! j) else True))"
    using assms(3) by presburger
  have **: "A = (\<Prod>j\<in>{i}. if j = i then A else 1)" by fastforce

  show ?thesis using replicate_pmf_indep'[OF 1 2 3, folded ** *] .
qed

lemma replicate_pmf_indep:
  fixes p :: "'a pmf"
  fixes n :: nat
  fixes E :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  defines "rp \<equiv> replicate_pmf n p"
  shows "prob_space.indep_events rp (\<lambda>i. {xs \<in> rp. E i (xs!i)}) {..<n}"
proof-
  define A where "A \<equiv> (\<lambda>i. pmf (p \<bind> (\<lambda>x. return_pmf (E i x))) True)"
  let ?I = "{..<n}"
  let ?S = "\<lambda>i. {xs \<in> rp. E i (xs!i)}"

  have 0: "prob_space rp" by unfold_locales
  have 1: "?S`?I \<subseteq> prob_space.events rp" by fastforce
  have 2: "(\<forall>J\<subseteq>?I.
      J \<noteq> {}
      \<longrightarrow> finite J
      \<longrightarrow> prob_space.prob rp (\<Inter>j\<in>J. ?S j) = (\<Prod>j\<in>J. prob_space.prob rp (?S j)))"
  proof clarify
    fix J assume *: "J \<subseteq> ?I" "J \<noteq> {}" "finite J"

    define E' where "E' \<equiv> (\<lambda>i x. (if i \<in> J then E i x else True))"
    define A' where "A' \<equiv> (\<lambda>i. (if i \<in> J then A i else 1))"

    have E'A': "\<forall>i<n. pmf (p \<bind> (\<lambda>x. return_pmf (E' i x))) True = A' i"
      unfolding A'_def E'_def A_def by force
    have A'_notin_J: "\<forall>i<n. i \<notin> J \<longrightarrow> A' i = 1" unfolding A'_def by presburger

    have "(\<Inter>j\<in>J. ?S j) = {xs \<in> rp. (\<forall>j \<in> J. E j (xs!j))}" using *(2) by blast
    hence "prob_space.prob rp (\<Inter>j\<in>J. ?S j) = prob_space.prob rp {xs \<in> rp. (\<forall>j \<in> J. E j (xs!j))}"
      by presburger
    also have "... = pmf (rp \<bind> (\<lambda>xs. return_pmf (\<forall>j \<in> J. E' j (xs!j)))) True"
      by (simp add: pmf_of_prop E'_def)
    also have "... = pmf (rp \<bind> (\<lambda>xs. return_pmf (\<forall>j<n. E' j (xs!j)))) True"
    proof-
      have "(\<lambda>xs. return_pmf (\<forall>j \<in> J. E' j (xs!j))) = (\<lambda>xs. return_pmf (\<forall>j<n. E' j (xs!j)))"
        unfolding E'_def using *(1) by fastforce
      thus ?thesis by presburger
    qed
    also have "... = (\<Prod>j\<in>J. A' j)"
      using replicate_pmf_indep'[OF E'A' *(1) A'_notin_J, folded rp_def] .
    also have "... = (\<Prod>j\<in>J. prob_space.prob rp (?S j))"
    proof-
      have "\<forall>j \<in> J. A' j = prob_space.prob rp (?S j)"
      proof
        fix j assume **: "j \<in> J"
        hence "A' j = A j" unfolding A'_def by presburger
        also have "... = pmf (p \<bind> (\<lambda>x. return_pmf (E j x))) True"
          unfolding A_def using *(1) ** by auto
        also have "... = pmf (rp \<bind> (\<lambda>xs. return_pmf (E j (xs ! j)))) True"
          using replicate_pmf_indep''[of j n p "E j", folded rp_def] *(1) ** by fastforce
        also have "... = prob_space.prob rp (?S j)" by (simp add: pmf_of_prop)
        finally show "A' j = prob_space.prob rp (?S j)" .
      qed
      thus ?thesis by force
    qed
    finally show "prob_space.prob rp (\<Inter>j\<in>J. ?S j) = (\<Prod>j\<in>J. prob_space.prob rp (?S j))" .
  qed
  have *: "?S`?I \<subseteq> prob_space.events rp \<and>
      (\<forall>J\<subseteq>?I. J \<noteq> {}
        \<longrightarrow> finite J
        \<longrightarrow> prob_space.prob rp (\<Inter>(?S ` J)) = (\<Prod>j\<in>J. prob_space.prob rp (?S j)))"
    using 1 2 by blast

  show ?thesis using prob_space.indep_events_def[OF 0] * by blast
qed

lemma replicate_spmf_same_event_leq:
  fixes p :: "'a spmf"
  fixes n :: nat
  fixes E :: "'a option \<Rightarrow> bool"
  assumes "spmf (p \<bind> (\<lambda>x. return_spmf (E x))) True \<le> A"
  shows "spmf (replicate_spmf n p \<bind> (\<lambda>xs. return_spmf (\<forall>i < n. E (xs!i)))) True \<le> A^n"
  by (metis replicate_spmf_same_event assms pmf_nonneg pow_mono)

lemma pmf_of_finite_set_event:
  fixes S :: "'a set"
  fixes p :: "'a pmf"
  fixes P :: "'a \<Rightarrow> bool"
  defines "p \<equiv> pmf_of_set S"
  assumes "S \<noteq> {}"
  assumes "finite S"
  shows "pmf (p \<bind> (\<lambda>t. return_pmf (P t))) True = (card ({t \<in> S. P t})) / card S"
proof-
  have *: "set_pmf p = S"
    using assms by auto
  have "pmf (p \<bind> (\<lambda>t. return_pmf (P t))) True = prob_space.prob p ({x \<in> set_pmf p. P x})"
    using pmf_of_prop[of p P] .
  also have "... = measure (measure_pmf (pmf_of_set S)) {x \<in> set_pmf p. P x}"
    by (simp add: assms(1))
  also have "... = card ({x \<in> set_pmf p. P x}) / card (set_pmf p)"
  proof-
    have "S \<inter> {x \<in> set_pmf p. P x} = {x \<in> set_pmf p. P x}" using * by blast
    thus ?thesis using measure_pmf_of_set[OF assms(2,3)] unfolding * by presburger
  qed
  also have "... = card ({t \<in> S. P t}) / card S" using assms by auto
  finally show ?thesis .
qed

lemma spmf_of_finite_set_event:
  fixes S :: "'a set"
  fixes p :: "'a spmf"
  fixes P :: "'a \<Rightarrow> bool"
  defines "p \<equiv> spmf_of_set S"
  assumes "finite S"
  shows "spmf (p \<bind> (\<lambda>t. return_spmf (P t))) True = (card ({t \<in> S. P t})) / card S"
proof-
  have "spmf (p \<bind> (\<lambda>t. return_spmf (P t))) True = prob_space.prob p (Some`{x \<in> set_spmf p. P x})"
    using spmf_of_prop[of p P] .
  also have "... = measure (measure_spmf (spmf_of_set S)) {x \<in> set_spmf p. P x}"
    by (simp add: assms(1) measure_measure_spmf_conv_measure_pmf)
  also have "... = card ({x \<in> set_spmf p. P x}) / card (set_spmf p)"
    using measure_spmf_of_set[of S "{x \<in> set_spmf p. P x}"]
    by (simp add: Collect_conj_eq assms(1,2))
  also have "... = card ({t \<in> S. P t}) / card S" using assms by simp
  finally show ?thesis .
qed

end