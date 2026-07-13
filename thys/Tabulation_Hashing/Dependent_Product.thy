theory Dependent_Product
  imports "HOL-Probability.Probability"
begin

text \<open>The following lemma was reproduced from \cite[Lemma \emph{measure\_pmf\_prob\_dependent\_product\_bound\_eq}]{Approximate_Model_Counting-AFP}
The AFP imports \verb|Monad_Normalisation.Monad_Normalisation| which alters some Isabelle syntax, which we want to avoid by copy pasting the lemmas here\<close>

lemma measure_pmf_prob_dependent_product_bound_eq:
  assumes "countable A" "\<And>i. countable (B i)"
  assumes "\<And>a. a \<in> A \<Longrightarrow> measure_pmf.prob N (B a) = r"
  shows "measure_pmf.prob (pair_pmf M N) (Sigma A B) = measure_pmf.prob M A * r"
    (is "?L = ?R")
proof -
  have "?L =
    (\<Sum>\<^sub>a(a, b) \<in> Sigma A B. pmf M a * pmf N b)"
    by (auto intro!: infsetsum_cong simp add: measure_pmf_conv_infsetsum pmf_pair)

  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. pmf M a * pmf N b)"
    apply (subst infsetsum_Sigma)
      using assms abs_summable_on_cong[of _ "pmf (pair_pmf M N)" "\<lambda>uub. pmf M (fst uub) * pmf N (snd uub)"] pmf_pair[of M N]
      by (fastforce simp: case_prod_beta)+

  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. pmf M a * (measure_pmf.prob N (B a)))"
    by (simp add: infsetsum_cmult_right measure_pmf_conv_infsetsum pmf_abs_summable)

  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. pmf M a * r)"
    using assms(3) by fastforce

  also have "\<dots> = ?R"
    by (simp add: infsetsum_cmult_left pmf_abs_summable measure_pmf_conv_infsetsum)

  finally show ?thesis .
qed

text \<open>The following lemma was reproduced from \cite[Lemma \emph{measure\_pmf\_prob\_dependent\_product\_bound\_eq'}]{Approximate_Model_Counting-AFP}
The AFP imports \verb|Monad_Normalisation.Monad_Normalisation| which alters some Isabelle syntax, which we want to avoid by copy pasting the lemmas here\<close>

lemma measure_pmf_prob_dependent_product_bound_eq':
  \<comment> \<open>N is the pmf we want to fix depending on values from M\<close>
  assumes "\<And>a. a \<in> A \<inter> set_pmf M \<Longrightarrow> measure_pmf.prob N (B a) = r"
  shows "measure_pmf.prob (pair_pmf M N) (Sigma A B) = measure_pmf.prob M A * r"
    (is "?L = ?R")
proof -
  have "Sigma A B \<inter> (set_pmf M \<times> set_pmf N) =
    Sigma (A \<inter> set_pmf M) (\<lambda>i. B i \<inter> set_pmf N)"
    by auto

  then have "?L =
    measure_pmf.prob (pair_pmf M N) (Sigma (A \<inter> set_pmf M) (\<lambda>i. B i \<inter> set_pmf N))"
    by (metis measure_Int_set_pmf set_pair_pmf)

  also have "\<dots> = measure_pmf.prob M (A \<inter> set_pmf M) * r"
    by (fastforce intro: measure_pmf_prob_dependent_product_bound_eq simp: assms measure_Int_set_pmf)

  also have "\<dots> = ?R" by (simp add: measure_Int_set_pmf)

  finally show ?thesis .
qed

end