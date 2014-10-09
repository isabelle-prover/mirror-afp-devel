(*
  Authors: Johannes Hölzl, Manuel Eberl
  Defines the subprobability spaces, the kernel space and the Giry monad 
  on subprobability spaces.
*)

header {* Giry Monad *}

theory Giry_Monad
  imports Probability "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Sub-probability spaces *}

locale subprob_space = finite_measure +
  assumes emeasure_space_le_1: "emeasure M (space M) \<le> 1"
  assumes not_empty: "space M \<noteq> {}"

lemma subprob_spaceI[Pure.intro!]:
  assumes *: "emeasure M (space M) \<le> 1"
  assumes "space M \<noteq> {}"
  shows "subprob_space M"
proof -
  interpret finite_measure M
  proof
    show "emeasure M (space M) \<noteq> \<infinity>" using * by auto
  qed
  show "subprob_space M" by default fact+
qed

lemma prob_space_imp_subprob_space:
  "prob_space M \<Longrightarrow> subprob_space M"
  by (rule subprob_spaceI) (simp_all add: prob_space.emeasure_space_1 prob_space.not_empty)

sublocale prob_space \<subseteq> subprob_space
  by (rule subprob_spaceI) (simp_all add: emeasure_space_1 not_empty)

lemma (in subprob_space) subprob_space_distr:
  assumes f: "f \<in> measurable M M'" and "space M' \<noteq> {}" shows "subprob_space (distr M M' f)"
proof (rule subprob_spaceI)
  have "f -` space M' \<inter> space M = space M" using f by (auto dest: measurable_space)
  with f show "emeasure (distr M M' f) (space (distr M M' f)) \<le> 1"
    by (auto simp: emeasure_distr emeasure_space_le_1)
  show "space (distr M M' f) \<noteq> {}" by (simp add: assms)
qed

lemma (in subprob_space) measure_le_1: "emeasure M X \<le> 1"
  by (rule order.trans[OF emeasure_space emeasure_space_le_1])

locale pair_subprob_space = 
  pair_sigma_finite M1 M2 + M1: subprob_space M1 + M2: subprob_space M2 for M1 M2

sublocale pair_subprob_space \<subseteq> P: subprob_space "M1 \<Otimes>\<^sub>M M2"
proof
  have "\<And>a b. \<lbrakk>a \<ge> 0; b \<ge> 0; a \<le> 1; b \<le> 1\<rbrakk> \<Longrightarrow> a * b \<le> (1::ereal)"
    by (metis comm_monoid_mult_class.mult.left_neutral dual_order.trans ereal_mult_right_mono)
  from this[OF _ _ M1.emeasure_space_le_1 M2.emeasure_space_le_1]
    show "emeasure (M1 \<Otimes>\<^sub>M M2) (space (M1 \<Otimes>\<^sub>M M2)) \<le> 1"
    by (simp add: M2.emeasure_pair_measure_Times space_pair_measure emeasure_nonneg)
  from M1.not_empty and M2.not_empty show "space (M1 \<Otimes>\<^sub>M M2) \<noteq> {}"
    by (simp add: space_pair_measure)
qed



definition "smallest_measurable X F = sigma X {f -` A \<inter> X | f M A. (f, M) \<in> F \<and> A \<in> sets M}"

lemma sets_smallest_measurable:
  "(f, M) \<in> F \<Longrightarrow> A \<in> sets M \<Longrightarrow> f -` A \<inter> X \<in> sets (smallest_measurable X F)"
  by (auto simp: smallest_measurable_def)

lemma space_smallest_measurable: "space (smallest_measurable X F) = X"
  by (simp add: space_measure_of_conv smallest_measurable_def)

lemma measurable_smallest_measurable1:
  "(f, M) \<in> F \<Longrightarrow> f \<in> X \<rightarrow> space M \<Longrightarrow> f \<in> measurable (smallest_measurable X F) M"
  by (simp add: measurable_def sets_smallest_measurable space_smallest_measurable)

lemma measurable_smallest_measurable2:
  assumes F: "\<And>f M. (f, M) \<in> F \<Longrightarrow> (\<lambda>x. f (S x)) \<in> measurable N M"
    and S: "S \<in> space N \<rightarrow> X"
  shows "S \<in> measurable N (smallest_measurable X F)"
  unfolding smallest_measurable_def
proof (rule measurable_measure_of)
  fix A assume "A \<in> {f -` A \<inter> X |f M A. (f, M) \<in> F \<and> A \<in> sets M}"
  then obtain f M A' where A': "(f, M) \<in> F" "A' \<in> sets M" and "A = f -` A' \<inter> X"
    by auto
  then have "S -` A \<inter> space N = (\<lambda>x. f (S x)) -` A' \<inter> space N"
    using S by auto
  also have "\<dots> \<in> sets N"
    by (rule measurable_sets F A')+
  finally show "S -` A \<inter> space N \<in> sets N" .
qed (auto simp: S)


definition "kernel_space A =
  smallest_measurable {M. subprob_space M \<and> sets M = sets A} {(\<lambda>M. emeasure M a, borel) | a. a \<in> sets A}"

lemma space_kernel_space: "space (kernel_space A) = {M. subprob_space M \<and> sets M = sets A}"
  by (simp add: kernel_space_def space_smallest_measurable) 

lemma measurable_emeasure_kernel_space[measurable]: 
    "a \<in> sets A \<Longrightarrow> (\<lambda>M. emeasure M a) \<in> borel_measurable (kernel_space A)"
  unfolding kernel_space_def by (rule measurable_smallest_measurable1) auto

context
  fixes K M N assumes K: "K \<in> measurable M (kernel_space N)"
begin

lemma subprob_space_kernel: "a \<in> space M \<Longrightarrow> subprob_space (K a)"
  using measurable_space[OF K] by (simp add: space_kernel_space)

lemma sets_kernel: "a \<in> space M \<Longrightarrow> sets (K a) = sets N"
  using measurable_space[OF K] by (simp add: space_kernel_space)

lemma measurable_emeasure_kernel[measurable]: 
    "A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M"
  using measurable_compose[OF K measurable_emeasure_kernel_space] .

end

lemma measurable_kernel_space:
  "(\<And>a. a \<in> space M \<Longrightarrow> subprob_space (K a)) \<Longrightarrow>
  (\<And>a. a \<in> space M \<Longrightarrow> sets (K a) = sets N) \<Longrightarrow>
  (\<And>A. A \<in> sets N \<Longrightarrow> (\<lambda>a. emeasure (K a) A) \<in> borel_measurable M) \<Longrightarrow>
  K \<in> measurable M (kernel_space N)"
  unfolding kernel_space_def by (subst measurable_smallest_measurable2) auto

subsection {* Properties of return *}

definition return :: "'a measure \<Rightarrow> 'a \<Rightarrow> 'a measure" where
  "return R x = measure_of (space R) (sets R) (\<lambda>A. indicator A x)"

lemma space_return[simp]: "space (return M x) = space M"
  by (simp add: return_def)

lemma sets_return[simp]: "sets (return M x) = sets M"
  by (simp add: return_def)

lemma measurable_return1[simp]: "measurable (return N x) L = measurable N L"
  by (simp cong: measurable_cong_sets) 

lemma measurable_return2[simp]: "measurable L (return N x) = measurable L N"
  by (simp cong: measurable_cong_sets) 

lemma emeasure_return[simp]:
  assumes "A \<in> sets M"
  shows "emeasure (return M x) A = indicator A x"
proof (rule emeasure_measure_of[OF return_def])
  show "sets M \<subseteq> Pow (space M)" by (rule sets.space_closed)
  show "positive (sets (return M x)) (\<lambda>A. indicator A x)" by (simp add: positive_def)
  from assms show "A \<in> sets (return M x)" unfolding return_def by simp
  show "countably_additive (sets (return M x)) (\<lambda>A. indicator A x)"
    by (auto intro: countably_additiveI simp: suminf_indicator)
qed

lemma prob_space_return: "x \<in> space M \<Longrightarrow> prob_space (return M x)"
  by rule simp

lemma subprob_space_return: "x \<in> space M \<Longrightarrow> subprob_space (return M x)"
  by (intro prob_space_return prob_space_imp_subprob_space)

lemma AE_return:
  assumes [simp]: "x \<in> space M" and [measurable]: "Measurable.pred M P"
  shows "(AE y in return M x. P y) \<longleftrightarrow> P x"
proof -
  have "(AE y in return M x. y \<notin> {x\<in>space M. \<not> P x}) \<longleftrightarrow> P x"
    by (subst AE_iff_null_sets[symmetric]) (simp_all add: null_sets_def split: split_indicator)
  also have "(AE y in return M x. y \<notin> {x\<in>space M. \<not> P x}) \<longleftrightarrow> (AE y in return M x. P y)"
    by (rule AE_cong) auto
  finally show ?thesis .
qed
  
lemma nn_integral_return:
  assumes "g x \<ge> 0" "x \<in> space M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ a. g a \<partial>return M x) = g x"
proof-
  interpret prob_space "return M x" by (rule prob_space_return[OF `x \<in> space M`])
  have "(\<integral>\<^sup>+ a. g a \<partial>return M x) = (\<integral>\<^sup>+ a. g x \<partial>return M x)" using assms
    by (intro nn_integral_cong_AE) (auto simp: AE_return)
  also have "... = g x"
    using nn_integral_const[OF `g x \<ge> 0`, of "return M x"] emeasure_space_1 by simp
  finally show ?thesis .
qed

lemma return_measurable: "return N \<in> measurable N (kernel_space N)"
  by (rule measurable_kernel_space) (auto simp: subprob_space_return)

lemma distr_return:
  assumes "f \<in> measurable M N" and "x \<in> space M"
  shows "distr (return M x) N f = return N (f x)"
  using assms by (intro measure_eqI) (simp_all add: indicator_def emeasure_distr)

definition "select_sets M = (SOME N. sets M = sets (kernel_space N))"

lemma select_sets1:
  "sets M = sets (kernel_space N) \<Longrightarrow> sets M = sets (kernel_space (select_sets M))"
  unfolding select_sets_def by (rule someI)

lemma space_empty_iff: "space N = {} \<longleftrightarrow> sets N = {{}}"
  by (metis Pow_empty Sup_bot_conv(1) cSup_singleton empty_iff sets.sigma_sets_eq sets.space_closed sigma_sets_top subset_singletonD)

lemma space_kernel_space_empty_iff:
  "space (kernel_space N) = {} \<longleftrightarrow> space N = {}"
proof
  have "\<And>x. x \<in> space N \<Longrightarrow> return N x \<in> space (kernel_space N)"
    by (auto simp: space_kernel_space subprob_space_return)
  then show "space (kernel_space N) = {} \<Longrightarrow> space N = {}"
    by auto
next
  assume "space N = {}"
  hence "sets N = {{}}" by (simp add: space_empty_iff)
  moreover have "\<And>M. subprob_space M \<Longrightarrow> sets M \<noteq> {{}}"
    by (simp add: subprob_space.not_empty space_empty_iff[symmetric])
  ultimately show "space (kernel_space N) = {}" by (auto simp: space_kernel_space)
qed

lemma sets_select_sets[simp]:
  assumes sets: "sets M = sets (kernel_space N)"
  shows "sets (select_sets M) = sets N"
  unfolding select_sets_def
proof (rule someI2)
  show "sets M = sets (kernel_space N)"
    by fact
next
  fix L assume "sets M = sets (kernel_space L)"
  with sets have eq: "space (kernel_space N) = space (kernel_space L)"
    by (intro sets_eq_imp_space_eq) simp
  show "sets L = sets N"
  proof cases
    assume "space (kernel_space N) = {}"
    with space_kernel_space_empty_iff[of N] space_kernel_space_empty_iff[of L]
    show ?thesis
      by (simp add: eq space_empty_iff)
  next
    assume "space (kernel_space N) \<noteq> {}"
    with eq show ?thesis
      by (fastforce simp add: space_kernel_space)
  qed
qed

lemma space_select_sets[simp]:
  "sets M = sets (kernel_space N) \<Longrightarrow> space (select_sets M) = space N"
  by (intro sets_eq_imp_space_eq sets_select_sets)

(* TODO: Move *)
lemma kernel_space_cong: "sets M = sets N \<Longrightarrow> kernel_space M = kernel_space N"
  by (simp add: kernel_space_def)

(* TODO: Move *)
lemma space_empty: "space M = {} \<Longrightarrow> M = count_space {}"
  by (rule measure_eqI) (simp_all add: space_empty_iff)

(* TODO: Move *)
lemma measurable_empty_iff: 
  "space N = {} \<Longrightarrow> f \<in> measurable M N \<longleftrightarrow> space M = {}"
  by (auto simp add: measurable_def Pi_iff)

lemma measurable_distr:
  assumes [measurable]: "f \<in> measurable M N"
  shows "(\<lambda>M'. distr M' N f) \<in> measurable (kernel_space M) (kernel_space N)"
proof (cases "space N = {}")
  assume not_empty: "space N \<noteq> {}"
  show ?thesis unfolding kernel_space_def[of N]
  proof (safe intro!: measurable_smallest_measurable2)
    fix A assume A: "A \<in> sets N"
    then have "(\<lambda>M'. emeasure (distr M' N f) A) \<in> borel_measurable (kernel_space M) \<longleftrightarrow>
      (\<lambda>M'. emeasure M' (f -` A \<inter> space M)) \<in> borel_measurable (kernel_space M)"
      by (intro measurable_cong)
         (auto simp: emeasure_distr space_kernel_space dest: sets_eq_imp_space_eq cong: measurable_cong)
    also have "\<dots>"
      using A by (intro measurable_emeasure_kernel_space) simp
    finally show "(\<lambda>M'. emeasure (distr M' N f) A) \<in> borel_measurable (kernel_space M)" .
  qed (auto intro!: subprob_space.subprob_space_distr simp: space_kernel_space not_empty)
thm measurable_empty_iff
qed (insert assms, auto simp: measurable_empty_iff space_kernel_space_empty_iff)


subsection {* Join *}

definition join :: "'a measure measure \<Rightarrow> 'a measure" where
  "join M = measure_of (space (select_sets M)) (sets (select_sets M)) (\<lambda>B. \<integral>\<^sup>+ M'. emeasure M' B \<partial>M)"

lemma
  shows space_join[simp]: "space (join M) = space (select_sets M)"
    and sets_join[simp]: "sets (join M) = sets (select_sets M)"
  by (simp_all add: join_def)

lemma emeasure_join:
  assumes M[simp]: "sets M = sets (kernel_space N)" and A: "A \<in> sets N"
  shows "emeasure (join M) A = (\<integral>\<^sup>+ M'. emeasure M' A \<partial>M)"
proof (rule emeasure_measure_of[OF join_def])
  have eq: "borel_measurable M = borel_measurable (kernel_space N)"
    by auto
  show "countably_additive (sets (join M)) (\<lambda>B. \<integral>\<^sup>+ M'. emeasure M' B \<partial>M)"
  proof (rule countably_additiveI)
    fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets (join M)" "disjoint_family A"
    have "(\<Sum>i. \<integral>\<^sup>+ M'. emeasure M' (A i) \<partial>M) = (\<integral>\<^sup>+M'. (\<Sum>i. emeasure M' (A i)) \<partial>M)"
      using A by (subst nn_integral_suminf) (auto simp: measurable_emeasure_kernel_space eq)
    also have "\<dots> = (\<integral>\<^sup>+M'. emeasure M' (\<Union>i. A i) \<partial>M)"
    proof (rule nn_integral_cong)
      fix M' assume "M' \<in> space M"
      then show "(\<Sum>i. emeasure M' (A i)) = emeasure M' (\<Union>i. A i)"
        using A sets_eq_imp_space_eq[OF M] by (simp add: suminf_emeasure space_kernel_space)
    qed
    finally show "(\<Sum>i. \<integral>\<^sup>+M'. emeasure M' (A i) \<partial>M) = (\<integral>\<^sup>+M'. emeasure M' (\<Union>i. A i) \<partial>M)" .
  qed
qed (auto simp: A sets.space_closed positive_def nn_integral_nonneg)

lemma nn_integral_measurable_kernel_space:
  assumes f: "f \<in> borel_measurable N" "\<And>x. 0 \<le> f x"
  shows "(\<lambda>M. integral\<^sup>N M f) \<in> borel_measurable (kernel_space N)" (is "_ \<in> ?B")
  using f
proof induct
  case (cong f g)
  moreover have "(\<lambda>M'. \<integral>\<^sup>+M''. f M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. \<integral>\<^sup>+M''. g M'' \<partial>M') \<in> ?B"
    by (intro measurable_cong nn_integral_cong cong)
       (auto simp: space_kernel_space dest!: sets_eq_imp_space_eq)
  ultimately show ?case by simp
next
  case (set B)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. indicator B M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. emeasure M' B) \<in> ?B"
    by (intro measurable_cong nn_integral_indicator) (simp add: space_kernel_space)
  ultimately show ?case
    by (simp add: measurable_emeasure_kernel_space)
next
  case (mult f c)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. c * f M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. c * \<integral>\<^sup>+M''. f M'' \<partial>M') \<in> ?B"
    by (intro measurable_cong nn_integral_cmult) (simp add: space_kernel_space)
  ultimately show ?case
    by simp
next
  case (add f g)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. f M'' + g M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. (\<integral>\<^sup>+M''. f M'' \<partial>M') + (\<integral>\<^sup>+M''. g M'' \<partial>M')) \<in> ?B"
    by (intro measurable_cong nn_integral_add) (simp_all add: space_kernel_space)
  ultimately show ?case
    by (simp add: ac_simps)
next
  case (seq F)
  moreover then have "(\<lambda>M'. \<integral>\<^sup>+M''. (SUP i. F i) M'' \<partial>M') \<in> ?B \<longleftrightarrow> (\<lambda>M'. SUP i. (\<integral>\<^sup>+M''. F i M'' \<partial>M')) \<in> ?B"
    unfolding SUP_apply
    by (intro measurable_cong nn_integral_monotone_convergence_SUP) (simp_all add: space_kernel_space)
  ultimately show ?case
    by (simp add: ac_simps)
qed


lemma measurable_join:
  "join \<in> measurable (kernel_space (kernel_space N)) (kernel_space N)"
proof (cases "space N \<noteq> {}", rule measurable_kernel_space)
  fix A assume "A \<in> sets N"
  let ?B = "borel_measurable (kernel_space (kernel_space N))"
  have "(\<lambda>M'. emeasure (join M') A) \<in> ?B \<longleftrightarrow> (\<lambda>M'. (\<integral>\<^sup>+ M''. emeasure M'' A \<partial>M')) \<in> ?B"
  proof (rule measurable_cong)
    fix M' assume "M' \<in> space (kernel_space (kernel_space N))"
    then show "emeasure (join M') A = (\<integral>\<^sup>+ M''. emeasure M'' A \<partial>M')"
      by (intro emeasure_join) (auto simp: space_kernel_space `A\<in>sets N`)
  qed
  also have "(\<lambda>M'. \<integral>\<^sup>+M''. emeasure M'' A \<partial>M') \<in> ?B"
    using measurable_emeasure_kernel_space[OF `A\<in>sets N`] emeasure_nonneg[of _ A]
    by (rule nn_integral_measurable_kernel_space)
  finally show "(\<lambda>M'. emeasure (join M') A) \<in> borel_measurable (kernel_space (kernel_space N))" .
next
  assume [simp]: "space N \<noteq> {}"
  fix M assume M: "M \<in> space (kernel_space (kernel_space N))"
  then have "(\<integral>\<^sup>+M'. emeasure M' (space N) \<partial>M) \<le> (\<integral>\<^sup>+M'. 1 \<partial>M)"
    apply (intro nn_integral_mono)
    apply (auto simp: space_kernel_space 
                 dest!: sets_eq_imp_space_eq subprob_space.emeasure_space_le_1)
    done
  with M show "subprob_space (join M)"
    by (intro subprob_spaceI)
       (auto simp: emeasure_join space_kernel_space M assms dest: subprob_space.emeasure_space_le_1)
next
  assume "\<not>(space N \<noteq> {})"
  thus ?thesis by (simp add: measurable_empty_iff space_kernel_space_empty_iff)
qed (auto simp: space_kernel_space)

lemma nn_integral_join:
  assumes f: "f \<in> borel_measurable N" "\<And>x. 0 \<le> f x" and M: "sets M = sets (kernel_space N)"
  shows "(\<integral>\<^sup>+x. f x \<partial>join M) = (\<integral>\<^sup>+M'. \<integral>\<^sup>+x. f x \<partial>M' \<partial>M)"
  using f
proof induct
  case (cong f g)
  moreover have "integral\<^sup>N (join M) f = integral\<^sup>N (join M) g"
    by (intro nn_integral_cong cong) (simp add: M)
  moreover from M have "(\<integral>\<^sup>+ M'. integral\<^sup>N M' f \<partial>M) = (\<integral>\<^sup>+ M'. integral\<^sup>N M' g \<partial>M)"
    by (intro nn_integral_cong cong)
       (auto simp add: space_kernel_space dest!: sets_eq_imp_space_eq)
  ultimately show ?case
    by simp
next
  case (set A)
  moreover with M have "(\<integral>\<^sup>+ M'. integral\<^sup>N M' (indicator A) \<partial>M) = (\<integral>\<^sup>+ M'. emeasure M' A \<partial>M)" 
    by (intro nn_integral_cong nn_integral_indicator)
       (auto simp: space_kernel_space dest!: sets_eq_imp_space_eq)
  ultimately show ?case
    using M by (simp add: emeasure_join)
next
  case (mult f c)
  have "(\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. c * f x \<partial>M' \<partial>M) = (\<integral>\<^sup>+ M'. c * \<integral>\<^sup>+ x. f x \<partial>M' \<partial>M)"
    using mult M
    by (intro nn_integral_cong nn_integral_cmult)
       (auto simp add: space_kernel_space cong: measurable_cong dest!: sets_eq_imp_space_eq)
  also have "\<dots> = c * (\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. f x \<partial>M' \<partial>M)"
    using nn_integral_measurable_kernel_space[OF mult(3,4)]
    by (intro nn_integral_cmult mult) (simp add: M)
  also have "\<dots> = c * (integral\<^sup>N (join M) f)"
    by (simp add: mult)
  also have "\<dots> = (\<integral>\<^sup>+ x. c * f x \<partial>join M)"
    using mult(2,3) by (intro nn_integral_cmult[symmetric] mult) (simp add: M)
  finally show ?case by simp
next
  case (add f g)
  have "(\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. f x + g x \<partial>M' \<partial>M) = (\<integral>\<^sup>+ M'. (\<integral>\<^sup>+ x. f x \<partial>M') + (\<integral>\<^sup>+ x. g x \<partial>M') \<partial>M)"
    using add M
    by (intro nn_integral_cong nn_integral_add)
       (auto simp add: space_kernel_space cong: measurable_cong dest!: sets_eq_imp_space_eq)
  also have "\<dots> = (\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. f x \<partial>M' \<partial>M) + (\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. g x \<partial>M' \<partial>M)"
    using nn_integral_measurable_kernel_space[OF add(1,2)]
    using nn_integral_measurable_kernel_space[OF add(5,6)]
    by (intro nn_integral_add add) (simp_all add: M nn_integral_nonneg)
  also have "\<dots> = (integral\<^sup>N (join M) f) + (integral\<^sup>N (join M) g)"
    by (simp add: add)
  also have "\<dots> = (\<integral>\<^sup>+ x. f x + g x \<partial>join M)"
    using add by (intro nn_integral_add[symmetric] add) (simp_all add: M)
  finally show ?case by (simp add: ac_simps)
next
  case (seq F)
  have "(\<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. (SUP i. F i) x \<partial>M' \<partial>M) = (\<integral>\<^sup>+ M'. (SUP i. \<integral>\<^sup>+ x. F i x \<partial>M') \<partial>M)"
    using seq M unfolding SUP_apply
    by (intro nn_integral_cong nn_integral_monotone_convergence_SUP)
       (auto simp add: space_kernel_space cong: measurable_cong dest!: sets_eq_imp_space_eq)
  also have "\<dots> = (SUP i. \<integral>\<^sup>+ M'. \<integral>\<^sup>+ x. F i x \<partial>M' \<partial>M)"
    using nn_integral_measurable_kernel_space[OF seq(1,2)] seq
    by (intro nn_integral_monotone_convergence_SUP)
       (simp_all add: M nn_integral_nonneg incseq_nn_integral incseq_def le_fun_def nn_integral_mono )
  also have "\<dots> = (SUP i. integral\<^sup>N (join M) (F i))"
    by (simp add: seq)
  also have "\<dots> = (\<integral>\<^sup>+ x. (SUP i. F i x) \<partial>join M)"
    using seq by (intro nn_integral_monotone_convergence_SUP[symmetric] seq) (simp_all add: M)
  finally show ?case by (simp add: ac_simps)
qed

lemma join_assoc:
  assumes M: "sets M = sets (kernel_space (kernel_space N))"
  shows "join (distr M (kernel_space N) join) = join (join M)"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (join (distr M (kernel_space N) join))"
  then have A: "A \<in> sets N" by simp
  show "emeasure (join (distr M (kernel_space N) join)) A = emeasure (join (join M)) A"
    using measurable_join[of N]
    by (auto simp: M A nn_integral_distr emeasure_join measurable_emeasure_kernel_space emeasure_nonneg
                   sets_eq_imp_space_eq[OF M] space_kernel_space nn_integral_join[OF _ _ M]
             intro!: nn_integral_cong emeasure_join cong: measurable_cong)
qed (simp add: M)

lemma join_return: 
  assumes "sets M = sets N" and "subprob_space M"
  shows "join (return (kernel_space N) M) = M"
  by (rule measure_eqI)
     (simp_all add: emeasure_join emeasure_nonneg space_kernel_space  
                    measurable_emeasure_kernel_space nn_integral_return assms)

lemma join_return':
  assumes "sets N = sets M"
  shows "join (distr M (kernel_space N) (return N)) = M"
apply (rule measure_eqI)
apply (simp add: assms)
apply (subgoal_tac "return N \<in> measurable M (kernel_space N)")
apply (simp add: emeasure_join nn_integral_distr measurable_emeasure_kernel_space assms)
apply (subst measurable_cong_sets, rule assms[symmetric], rule refl, rule return_measurable)
done

lemma join_distr_distr:
  fixes f :: "'a \<Rightarrow> 'b" and M :: "'a measure measure" and N :: "'b measure"
  assumes "sets M = sets (kernel_space R)" and "f \<in> measurable R N"
  shows "join (distr M (kernel_space N) (\<lambda>M. distr M N f)) = distr (join M) N f" (is "?r = ?l")
proof (rule measure_eqI)
  fix A assume "A \<in> sets ?r"
  hence A_in_N: "A \<in> sets N" by simp

  from assms have "f \<in> measurable (join M) N" 
      by (simp cong: measurable_cong_sets)
  moreover from assms and A_in_N have "f-`A \<inter> space R \<in> sets R" 
      by (intro measurable_sets) simp_all
  ultimately have "emeasure (distr (join M) N f) A = \<integral>\<^sup>+M'. emeasure M' (f-`A \<inter> space R) \<partial>M"
      by (simp_all add: A_in_N emeasure_distr emeasure_join assms)
  
  also have "... = \<integral>\<^sup>+ x. emeasure (distr x N f) A \<partial>M" using A_in_N
  proof (intro nn_integral_cong, subst emeasure_distr)
    fix M' assume "M' \<in> space M"
    from assms have "space M = space (kernel_space R)"
        using sets_eq_imp_space_eq by blast
    with `M' \<in> space M` have [simp]: "sets M' = sets R" using space_kernel_space by blast
    show "f \<in> measurable M' N" by (simp cong: measurable_cong_sets add: assms)
    have "space M' = space R" by (rule sets_eq_imp_space_eq) simp
    thus "emeasure M' (f -` A \<inter> space R) = emeasure M' (f -` A \<inter> space M')" by simp
  qed

  also have "(\<lambda>M. distr M N f) \<in> measurable M (kernel_space N)"
      by (simp cong: measurable_cong_sets add: assms measurable_distr)
  hence "(\<integral>\<^sup>+ x. emeasure (distr x N f) A \<partial>M) = 
             emeasure (join (distr M (kernel_space N) (\<lambda>M. distr M N f))) A"
      by (simp_all add: emeasure_join assms A_in_N nn_integral_distr measurable_emeasure_kernel_space)
  finally show "emeasure ?r A = emeasure ?l A" ..
qed simp

definition bind :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b measure) \<Rightarrow> 'b measure" where
  "bind M f = (if space M = {} then count_space {} else
    join (distr M (kernel_space (f (SOME x. x \<in> space M))) f))"

adhoc_overloading Monad_Syntax.bind bind

lemma bind_empty: 
  "space M = {} \<Longrightarrow> bind M f = count_space {}"
  by (simp add: bind_def)

lemma bind_nonempty:
  "space M \<noteq> {} \<Longrightarrow> bind M f = join (distr M (kernel_space (f (SOME x. x \<in> space M))) f)"
  by (simp add: bind_def)

lemma sets_bind_empty: "sets M = {} \<Longrightarrow> sets (bind M f) = {{}}"
  by (auto simp: bind_def)

lemma space_bind_empty: "space M = {} \<Longrightarrow> space (bind M f) = {}"
  by (simp add: bind_def)

lemma sets_bind[simp]: 
  assumes "f \<in> measurable M (kernel_space N)" and "space M \<noteq> {}"
  shows "sets (bind M f) = sets N"
    using assms(2) by (force simp: bind_nonempty intro!: sets_kernel[OF assms(1) someI_ex])

lemma space_bind[simp]: 
  assumes "f \<in> measurable M (kernel_space N)" and "space M \<noteq> {}"
  shows "space (bind M f) = space N"
    using assms by (intro sets_eq_imp_space_eq sets_bind)

lemma bind_cong: 
  assumes "\<forall>x \<in> space M. f x = g x"
  shows "bind M f = bind M g"
proof (cases "space M = {}")
  assume "space M \<noteq> {}"
  hence "(SOME x. x \<in> space M) \<in> space M" by (rule_tac someI_ex) blast
  with assms have "f (SOME x. x \<in> space M) = g (SOME x. x \<in> space M)" by blast
  with `space M \<noteq> {}` and assms show ?thesis by (simp add: bind_nonempty cong: distr_cong)
qed (simp add: bind_empty)

lemma bind_nonempty':
  assumes "f \<in> measurable M (kernel_space N)" "x \<in> space M"
  shows "bind M f = join (distr M (kernel_space N) f)"
  using assms
  apply (subst bind_nonempty, blast)
  apply (subst kernel_space_cong[OF sets_kernel[OF assms(1) someI_ex]], blast)
  apply (simp add: kernel_space_cong[OF sets_kernel[OF assms]])
  done

lemma bind_nonempty'':
  assumes "f \<in> measurable M (kernel_space N)" "space M \<noteq> {}"
  shows "bind M f = join (distr M (kernel_space N) f)"
  using assms by (auto intro: bind_nonempty')

lemma emeasure_bind:
    "\<lbrakk>space M \<noteq> {}; f \<in> measurable M (kernel_space N);X \<in> sets N\<rbrakk>
      \<Longrightarrow> emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. emeasure (f x) X \<partial>M"
  by (simp add: bind_nonempty'' emeasure_join nn_integral_distr measurable_emeasure_kernel_space)

lemma bind_return: 
  assumes "f \<in> measurable M (kernel_space N)" and "x \<in> space M"
  shows "bind (return M x) f = f x"
  using sets_kernel[OF assms] assms
  by (simp_all add: distr_return join_return subprob_space_kernel bind_nonempty'
               cong: kernel_space_cong)

lemma bind_return':
  shows "bind M (return M) = M"
  by (cases "space M = {}")
     (simp_all add: bind_empty space_empty[symmetric] bind_nonempty join_return' 
               cong: kernel_space_cong)

lemma bind_count_space_singleton:
  assumes "subprob_space (f x)"
  shows "count_space {x} \<guillemotright>= f = f x"
proof-
  have A: "\<And>A. A \<subseteq> {x} \<Longrightarrow> A = {} \<or> A = {x}" by auto
  have "count_space {x} = return (count_space {x}) x"
    by (intro measure_eqI) (auto dest: A)
  also have "... \<guillemotright>= f = f x"
    by (subst bind_return[of _ _ "f x"]) (auto simp: space_kernel_space assms)
  finally show ?thesis .
qed

(* TODO: Move *)
lemma ereal_indicator[simp]:
    "(\<lambda>x. ereal (indicator {v} x)) = indicator {v}"
  by (rule ext) (simp split: split_indicator)
(* End TODO *)

lemma emeasure_bind_const: 
    "space M \<noteq> {} \<Longrightarrow> X \<in> sets N \<Longrightarrow> subprob_space N \<Longrightarrow> 
         emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)"
  by (simp add: bind_nonempty emeasure_join nn_integral_distr 
                space_kernel_space measurable_emeasure_kernel_space emeasure_nonneg)

lemma emeasure_bind_const':
  assumes "subprob_space M" "subprob_space N"
  shows "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)"
using assms
proof (case_tac "X \<in> sets N")
  fix X assume "X \<in> sets N"
  thus "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)" using assms
      by (subst emeasure_bind_const) 
         (simp_all add: subprob_space.not_empty subprob_space.emeasure_space_le_1)
next
  fix X assume "X \<notin> sets N"
  with assms show "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X * emeasure M (space M)"
      by (simp add: sets_bind[of _ _ N] subprob_space.not_empty 
                    space_kernel_space emeasure_notin_sets)
qed

lemma emeasure_bind_const_prob_space:
  assumes "prob_space M" "subprob_space N"
  shows "emeasure (M \<guillemotright>= (\<lambda>x. N)) X = emeasure N X"
  using assms by (simp add: emeasure_bind_const' prob_space_imp_subprob_space 
                            prob_space.emeasure_space_1)

lemma bind_const': "\<lbrakk>prob_space M; subprob_space N\<rbrakk> \<Longrightarrow> M \<guillemotright>= (\<lambda>x. N) = N"
  by (intro measure_eqI) 
     (simp_all add: space_kernel_space prob_space.not_empty emeasure_bind_const_prob_space)

lemma bind_return_distr: 
    "space M \<noteq> {} \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> bind M (return N \<circ> f) = distr M N f"
  apply (simp add: bind_nonempty)
  apply (subst kernel_space_cong)
  apply (rule sets_return)
  apply (subst distr_distr[symmetric])
  apply (auto intro!: return_measurable simp: distr_distr[symmetric] join_return')
  done

lemma bind_assoc:
  fixes f :: "'a \<Rightarrow> 'b measure" and g :: "'b \<Rightarrow> 'c measure"
  assumes M1: "f \<in> measurable M (kernel_space N)" and M2: "g \<in> measurable N (kernel_space R)"
  shows "bind (bind M f) g = bind M (\<lambda>x. bind (f x) g)"
proof (cases "space M = {}")
  assume [simp]: "space M \<noteq> {}"
  from assms have [simp]: "space N \<noteq> {}" "space R \<noteq> {}"
      by (auto simp: measurable_empty_iff space_kernel_space_empty_iff)
  from assms have sets_fx[simp]: "\<And>x. x \<in> space M \<Longrightarrow> sets (f x) = sets N"
      by (simp add: sets_kernel)
  have ex_in: "\<And>A. A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A" by blast
  note sets_some[simp] = sets_kernel[OF M1 someI_ex[OF ex_in[OF `space M \<noteq> {}`]]]
                         sets_kernel[OF M2 someI_ex[OF ex_in[OF `space N \<noteq> {}`]]]
  note space_some[simp] = sets_eq_imp_space_eq[OF this(1)] sets_eq_imp_space_eq[OF this(2)]

  have "bind M (\<lambda>x. bind (f x) g) = 
        join (distr M (kernel_space R) (join \<circ> (\<lambda>x. (distr x (kernel_space R) g)) \<circ> f))"
    by (simp add: sets_eq_imp_space_eq[OF sets_fx] bind_nonempty o_def
             cong: kernel_space_cong distr_cong)
  also have "distr M (kernel_space R) (join \<circ> (\<lambda>x. (distr x (kernel_space R) g)) \<circ> f) =
             distr (distr (distr M (kernel_space N) f)
                          (kernel_space (kernel_space R))
                          (\<lambda>x. distr x (kernel_space R) g)) 
                   (kernel_space R) join"
      apply (subst distr_distr, 
             (blast intro: measurable_comp measurable_distr measurable_join M1 M2)+)+
      apply (simp add: o_assoc)
      done
  also have "join ... = bind (bind M f) g"
      by (simp add: join_assoc join_distr_distr M2 bind_nonempty cong: kernel_space_cong)
  finally show ?thesis ..
qed (simp add: bind_empty)

lemma emeasure_space_kernel_space[measurable]:
  "(\<lambda>a. emeasure a (space a)) \<in> borel_measurable (kernel_space N)"
proof-
  have "(\<lambda>a. emeasure a (space N)) \<in> borel_measurable (kernel_space N)" (is "?f \<in> ?M")
    by (rule measurable_emeasure_kernel_space) simp
  also have "?f \<in> ?M \<longleftrightarrow> (\<lambda>a. emeasure a (space a)) \<in> ?M"
    by (rule measurable_cong) (auto simp: space_kernel_space dest: sets_eq_imp_space_eq)
  finally show ?thesis .
qed

(* TODO: Rename. This name is too general – Manuel *)
lemma measurable_pair_measure:
  assumes f: "f \<in> measurable M (kernel_space N)"
  assumes g: "g \<in> measurable M (kernel_space L)"
  shows "(\<lambda>x. f x \<Otimes>\<^sub>M g x) \<in> measurable M (kernel_space (N \<Otimes>\<^sub>M L))"
proof (rule measurable_kernel_space)
  { fix x assume "x \<in> space M"
    with measurable_space[OF f] measurable_space[OF g]
    have fx: "f x \<in> space (kernel_space N)" and gx: "g x \<in> space (kernel_space L)"
      by auto
    interpret F: subprob_space "f x"
      using fx by (simp add: space_kernel_space)
    interpret G: subprob_space "g x"
      using gx by (simp add: space_kernel_space)

    interpret pair_subprob_space "f x" "g x" ..
    show "subprob_space (f x \<Otimes>\<^sub>M g x)" by unfold_locales
    show sets_eq: "sets (f x \<Otimes>\<^sub>M g x) = sets (N \<Otimes>\<^sub>M L)"
      using fx gx by (simp add: space_kernel_space)

    have 1: "\<And>A B. A \<in> sets N \<Longrightarrow> B \<in> sets L \<Longrightarrow> emeasure (f x \<Otimes>\<^sub>M g x) (A \<times> B) = emeasure (f x) A * emeasure (g x) B"
      using fx gx by (intro G.emeasure_pair_measure_Times) (auto simp: space_kernel_space) 
    have "emeasure (f x \<Otimes>\<^sub>M g x) (space (f x \<Otimes>\<^sub>M g x)) = 
              emeasure (f x) (space (f x)) * emeasure (g x) (space (g x))"
      by (subst G.emeasure_pair_measure_Times[symmetric]) (simp_all add: space_pair_measure)
    hence 2: "\<And>A. A \<in> sets (N \<Otimes>\<^sub>M L) \<Longrightarrow> emeasure (f x \<Otimes>\<^sub>M g x) (space N \<times> space L - A) =
                                             ... - emeasure (f x \<Otimes>\<^sub>M g x) A"
      using emeasure_compl[OF _ P.emeasure_finite]
      unfolding sets_eq
      unfolding sets_eq_imp_space_eq[OF sets_eq]
      by (simp add: space_pair_measure G.emeasure_pair_measure_Times)
    note 1 2 sets_eq }
  note Times = this(1) and Compl = this(2) and sets_eq = this(3)

  fix A assume A: "A \<in> sets (N \<Otimes>\<^sub>M L)"
  show "(\<lambda>a. emeasure (f a \<Otimes>\<^sub>M g a) A) \<in> borel_measurable M"
    using Int_stable_pair_measure_generator pair_measure_closed A
    unfolding sets_pair_measure
  proof (induct A rule: sigma_sets_induct_disjoint)
    case (basic A) then show ?case
      by (auto intro!: borel_measurable_ereal_times simp: Times cong: measurable_cong)
         (auto intro!: measurable_emeasure_kernel f g)
  next
    case (compl A)
    then have A: "A \<in> sets (N \<Otimes>\<^sub>M L)"
      by (auto simp: sets_pair_measure)
    have "(\<lambda>x. emeasure (f x) (space (f x)) * emeasure (g x) (space (g x)) - 
                   emeasure (f x \<Otimes>\<^sub>M g x) A) \<in> borel_measurable M" (is "?f \<in> ?M")
      using compl(2) f g by measurable
    thus ?case by (simp add: Compl A cong: measurable_cong)
  next
    case (union A)
    then have "range A \<subseteq> sets (N \<Otimes>\<^sub>M L)" "disjoint_family A"
      by (auto simp: sets_pair_measure)
    then have "(\<lambda>a. emeasure (f a \<Otimes>\<^sub>M g a) (\<Union>i. A i)) \<in> borel_measurable M \<longleftrightarrow>
      (\<lambda>a. \<Sum>i. emeasure (f a \<Otimes>\<^sub>M g a) (A i)) \<in> borel_measurable M"
      by (intro measurable_cong suminf_emeasure[symmetric])
         (auto simp: sets_eq)
    also have "\<dots>"
      using union by auto
    finally show ?case .
  qed simp
qed

(* TODO: Move *)
lemma measurable_distr2:
  assumes f[measurable]: "split f \<in> measurable (L \<Otimes>\<^sub>M M) N"
  assumes g[measurable]: "g \<in> measurable L (kernel_space M)"
  shows "(\<lambda>x. distr (g x) N (f x)) \<in> measurable L (kernel_space N)"
proof -
  have "(\<lambda>x. distr (g x) N (f x)) \<in> measurable L (kernel_space N)
    \<longleftrightarrow> (\<lambda>x. distr (return L x \<Otimes>\<^sub>M g x) N (split f)) \<in> measurable L (kernel_space N)"
  proof (rule measurable_cong)
    fix x assume x: "x \<in> space L"
    have gx: "g x \<in> space (kernel_space M)"
      using measurable_space[OF g x] .
    then have [simp]: "sets (g x) = sets M"
      by (simp add: space_kernel_space)
    then have [simp]: "space (g x) = space M"
      by (rule sets_eq_imp_space_eq)
    let ?R = "return L x"
    from measurable_compose_Pair1[OF x f] have f_M': "f x \<in> measurable M N"
      by simp
    interpret subprob_space "g x"
      using gx by (simp add: space_kernel_space)
    have space_pair_M'[simp]: "\<And>X. space (X \<Otimes>\<^sub>M g x) = space (X \<Otimes>\<^sub>M M)"
      by (simp add: space_pair_measure)
    show "distr (g x) N (f x) = distr (?R \<Otimes>\<^sub>M g x) N (split f)" (is "?l = ?r")
    proof (rule measure_eqI)
      show "sets ?l = sets ?r"
        by simp
    next
      fix A assume "A \<in> sets ?l"
      then have A[measurable]: "A \<in> sets N"
        by simp
      then have "emeasure ?r A = emeasure (?R \<Otimes>\<^sub>M g x) ((\<lambda>(x, y). f x y) -` A \<inter> space (?R \<Otimes>\<^sub>M g x))"
        by (auto simp add: emeasure_distr f_M' cong: measurable_cong_sets)
      also have "\<dots> = (\<integral>\<^sup>+M''. emeasure (g x) (f M'' -` A \<inter> space M) \<partial>?R)"
        apply (subst emeasure_pair_measure_alt)
        apply (rule measurable_sets[OF _ A])
        apply (auto simp add: f_M' cong: measurable_cong_sets)
        apply (intro nn_integral_cong arg_cong[where f="emeasure (g x)"])
        apply (auto simp: space_kernel_space space_pair_measure)
        done
      also have "\<dots> = emeasure (g x) (f x -` A \<inter> space M)"
        by (subst nn_integral_return)
           (auto simp: x intro!: measurable_emeasure)
      also have "\<dots> = emeasure ?l A"
        by (simp add: emeasure_distr f_M' cong: measurable_cong_sets)
      finally show "emeasure ?l A = emeasure ?r A" ..
    qed
  qed
  also have "\<dots>"
    apply (intro measurable_compose[OF measurable_pair_measure measurable_distr])
    apply (rule return_measurable)
    apply measurable
    done
  finally show ?thesis .
qed

(* END TODO *)

lemma measurable_bind':
  assumes M1: "f \<in> measurable M (kernel_space N)" and
          M2: "split g \<in> measurable (M \<Otimes>\<^sub>M N) (kernel_space R)"
  shows "(\<lambda>x. bind (f x) (g x)) \<in> measurable M (kernel_space R)"
proof (subst measurable_cong)
  fix x assume x_in_M: "x \<in> space M"
  with assms have "space (f x) \<noteq> {}" 
      by (blast dest: subprob_space_kernel subprob_space.not_empty)
  moreover from M2 x_in_M have "g x \<in> measurable (f x) (kernel_space R)"
      by (subst measurable_cong_sets[OF sets_kernel[OF M1 x_in_M] refl])
         (auto dest: measurable_Pair2)
  ultimately show "bind (f x) (g x) = join (distr (f x) (kernel_space R) (g x))" 
      by (simp_all add: bind_nonempty'')
next
  show "(\<lambda>w. join (distr (f w) (kernel_space R) (g w))) \<in> measurable M (kernel_space R)"
    apply (rule measurable_compose[OF _ measurable_join])
    apply (rule measurable_distr2[OF M2 M1])
    done
qed

lemma measurable_bind:
  assumes M1: "f \<in> measurable M (kernel_space N)" and
          M2: "(\<lambda>x. g (fst x) (snd x)) \<in> measurable (M \<Otimes>\<^sub>M N) (kernel_space R)"
  shows "(\<lambda>x. bind (f x) (g x)) \<in> measurable M (kernel_space R)"
  using assms by (auto intro: measurable_bind' simp: measurable_split_conv)

lemma measurable_bind2:
  assumes "f \<in> measurable M (kernel_space N)" and "g \<in> measurable N (kernel_space R)"
  shows "(\<lambda>x. bind (f x) g) \<in> measurable M (kernel_space R)"
    using assms by (intro measurable_bind' measurable_const) auto

lemma subprob_space_bind:
  assumes "subprob_space M" "f \<in> measurable M (kernel_space N)"
  shows "subprob_space (M \<guillemotright>= f)"
proof (rule subprob_space_kernel[of "\<lambda>x. x \<guillemotright>= f"])
  show "(\<lambda>x. x \<guillemotright>= f) \<in> measurable (kernel_space M) (kernel_space N)"
    by (rule measurable_bind, rule measurable_ident_sets, rule refl, 
        rule measurable_compose[OF measurable_snd assms(2)])
  from assms(1) show "M \<in> space (kernel_space M)"
    by (simp add: space_kernel_space)
qed

lemma double_bind_assoc:
  assumes Mg: "g \<in> measurable N (kernel_space N')"
  assumes Mf: "f \<in> measurable M (kernel_space M')"
  assumes Mh: "split h \<in> measurable (M \<Otimes>\<^sub>M M') N"
  shows "do {x \<leftarrow> M; y \<leftarrow> f x; g (h x y)} = do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g"
proof-
  have "do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g = 
            do {x \<leftarrow> M; do {y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g}"
    using Mh by (auto intro!: bind_assoc measurable_bind'[OF Mf] Mf Mg
                      measurable_compose[OF _ return_measurable] simp: measurable_split_conv)
  also from Mh have "\<And>x. x \<in> space M \<Longrightarrow> h x \<in> measurable M' N" by measurable
  hence "do {x \<leftarrow> M; do {y \<leftarrow> f x; return N (h x y)} \<guillemotright>= g} = 
            do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y) \<guillemotright>= g}"
    apply (intro ballI bind_cong bind_assoc)
    apply (subst measurable_cong_sets[OF sets_kernel[OF Mf] refl], simp)
    apply (rule measurable_compose[OF _ return_measurable], auto intro: Mg)
    done
  also have "\<And>x. x \<in> space M \<Longrightarrow> space (f x) = space M'"
    by (intro sets_eq_imp_space_eq sets_kernel[OF Mf])
  with measurable_space[OF Mh] 
    have "do {x \<leftarrow> M; y \<leftarrow> f x; return N (h x y) \<guillemotright>= g} = do {x \<leftarrow> M; y \<leftarrow> f x; g (h x y)}"
    by (intro ballI bind_cong bind_return[OF Mg]) (auto simp: space_pair_measure)
  finally show ?thesis ..
qed

end
