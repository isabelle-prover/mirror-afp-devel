(*  Title:   No_Free_Lunch_ML.thy
    Author:  Michikazu Hirata
*)
section \<open>No-Free-Lunch Theorem for ML\<close>
theory No_Free_Lunch_ML
imports
   "HOL-Probability.Probability"
begin

subsection \<open>Preliminaries\<close>

lemma sum_le_card_Max_of_nat:"finite A
 \<Longrightarrow> sum f A \<le> (of_nat :: _ \<Rightarrow> _ ::{semiring_1,ordered_comm_monoid_add}) (card A) * Max (f ` A)"
  using sum_bounded_above[of A f "Max (f ` A)"] by simp

lemma card_Min_le_sum_of_nat: "finite A
 \<Longrightarrow> (of_nat :: _ \<Rightarrow> _ ::{semiring_1,ordered_comm_monoid_add}) (card A) * Min (f ` A) \<le> sum f A"
  using sum_bounded_below[of A "Min (f ` A)" f] by simp

(* TODO: real to of_nat *)
text \<open> The following lemma is used to show the last equation of the proof of the no-free-lunch theorem
       in the book~\cite{shalev2014}.\<close>
text \<open> Let $A$ be a finite set. If $A$ is divided into the pairs $(x_1,y_1),\dots,(x_n,y_n)$
       such that $f(x_i) + f(y_i) = k$ for all $i = 1,\dots, n$.
       Then, we have $\sum_{x\in A} f(x) = k * |A| / 2$.\<close>
lemma sum_of_const_pairs:
  fixes k :: "real"
  assumes A:"finite A"
    and "fst ` B \<union> snd ` B = A" "fst ` B \<inter> snd ` B = {}"
    and "inj_on fst B" "inj_on snd B"
    and sum: "\<And>x y. (x,y) \<in> B \<Longrightarrow> f x + f y = k"
  shows "(\<Sum>x\<in>A. f x) = k * real (card A) / 2"
  using assms
proof(induction A arbitrary: B rule: finite_psubset_induct)
  case ih:(psubset A)
  show ?case
  proof(cases "A ={}")
    assume "A \<noteq> {}"
    then obtain x where x:"x \<in> A"
      by blast
    then obtain y where xy:"(x,y) \<in> B \<or> (y,x) \<in> B"
      using ih(3) by fastforce
    then have xy':"x \<noteq> y"
      by (metis emptyE fst_eqD ih(4) imageI mem_simps(4) snd_eqD)
    have y:"y \<in> A"
      using ih(3) xy by force
    have *:"(\<Sum>a\<in>A - {x,y}. f a) = k * real (card (A - {x,y})) / 2"
    proof -
      consider "(x,y) \<in> B" | "(y,x) \<in> B"
        using xy by blast
      then show ?thesis
      proof cases
        assume xy:"(x,y) \<in> B"
        show ?thesis
        proof(intro ih(2))
          have *:"fst ` (B - {(x, y)}) = fst ` B - {x}"
            by(subst inj_on_image_set_diff[of fst B]) (use ih(5) xy in auto)
          have **: "snd ` (B - {(x, y)}) = snd ` B - {y}"
            by(subst inj_on_image_set_diff[of snd B]) (use ih(6) xy in auto)
          have "x \<notin> snd ` B" "y \<notin> fst ` B"
            using ih(4) xy by(force simp: disjoint_iff)+
          thus "fst ` (B - {(x,y)}) \<union> snd ` (B - {(x,y)}) = A - {x,y}"
            using ih(3) by(auto simp: * **)
        qed(use x ih(4) in "auto intro!: inj_on_diff ih(5,6,7)")
      next
        assume xy:"(y,x) \<in> B"
        show ?thesis
        proof(intro ih(2))
          have *:"fst ` (B - {(y, x)}) = fst ` B - {y}"
            by(subst inj_on_image_set_diff[of fst B]) (use ih(5) xy in auto)
          have **: "snd ` (B - {(y, x)}) = snd ` B - {x}"
            by(subst inj_on_image_set_diff[of snd B]) (use ih(6) xy in auto)
          have "y \<notin> snd ` B" "x \<notin> fst ` B"
            using ih(4) xy by(force simp: disjoint_iff)+
          thus "fst ` (B - {(y,x)}) \<union> snd ` (B - {(y,x)}) = A - {x,y}"
            using ih(3) by(auto simp: * **)
        qed(use x ih(4) in "auto intro!: inj_on_diff ih(5,6,7)")
      qed
    qed
    have "(\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A - {x,y}. f a) + (f x + f y)"
      using x y xy' by (simp add: ih(1) sum_diff)
    also have "... = k * real (card (A - {x,y})) / 2 + (f x + f y)"
      by(simp add: *)
    also have "... = k * real (card (A - {x,y})) / 2 + k"
      using xy ih(7) by fastforce
    also have "... = k * real (card A) / 2"
      using x y xy' by(subst card_Diff_subset)
      (auto simp: of_nat_diff_if card_le_Suc0_iff_eq[OF ih(1)] not_less_eq_eq right_diff_distrib)
    finally show ?thesis .
  qed simp
qed

lemma(in prob_space) Markov_inequality_measure_minus:
  assumes "u \<in> borel_measurable M" and "AE x in M. 0 \<le> u x"  "AE x in M. 1 \<ge> u x"
    and [arith]: "0 < (a::real)"
  shows "\<P>(x in M. u x > 1 - a) \<ge> ((\<integral>x. u x \<partial>M) - (1 - a)) / a"
proof -
  have [measurable,simp]:"integrable M u"
    using assms by(auto intro!: integrable_const_bound[where B=1])
  have "measure M {x\<in>space M. u x \<le> 1 - a} = measure M {x\<in>space M. a \<le> 1 - u x}"
    by(rule arg_cong[where f="measure M"]) auto
  also have "... \<le> (\<integral>x. 1 - u x \<partial>M) / a"
    using assms by(intro integral_Markov_inequality_measure) auto
  finally have *:"measure M {x\<in>space M. u x \<le> 1 - a} \<le> (\<integral>x. 1 - u x \<partial>M) / a" .
  have "((\<integral>x. u x \<partial>M) - (1 - a)) / a = 1 - (\<integral>x. 1 - u x \<partial>M) / a"
    by (auto simp : prob_space diff_divide_distrib)
  also have "... \<le> 1 - measure M {x\<in>space M. u x \<le> 1 - a}"
    using * by simp
  also have "... = measure M {x\<in>space M. \<not> u x \<le> 1 - a}"
    by(intro prob_neg[symmetric]) simp
  also have "... = measure M {x\<in>space M. u x > 1 - a}"
    by(rule arg_cong[where f="measure M"]) auto
  finally show ?thesis .
qed

subsection \<open>No-Free-Lunch Theorem\<close>
text \<open> In our implementation, a learning algorithm of binary clasification
       is represented as a function
       $A :$ @{typ \<open>nat \<Rightarrow> (nat \<Rightarrow> 'a \<times> bool) \<Rightarrow> 'a \<Rightarrow> bool\<close>}
       where the first argument is the number of training data,
       the second argument is the training data (\isa{S\ n}$= (x_n, y_n)$ denotes the \isa{n}th data for
       a training data \isa{S}),
       and \isa{A\ m\ S} is a predictor.
       The first argument, which denotes the number of training data,
       is normally used to specify the number of loop executions in learning algorithm.
       In this formalization, we omit the first argument
       because we do not need the concrete definitions of learning algorithms.\<close>
text \<open> Let $X$ be the domain set.
       In order to analyze the error of predictors, we assume that each data $(x,y)$ is obtained from
       a distribution $\mathcal{D}$ on $X\times \mathbb{B}$.
       The error of a predictor $f$ with respect to $\mathcal{D}$ is defined as follows.
       \begin{align*}
          \mathcal{L}_{\mathcal{D}}(f) &\stackrel{\text{def}}{=} \mathop{\mathrm{P}}_{(x,y)\sim \mathcal{D}}(f(x) \neq y) \\
          &= \mathcal{D}(\{(x,y)\in X\times \mathbb{B}\mid f(x)\neq y\})
       \end{align*}\<close>
text \<open> In these settings, the no-free-lunch theorem states that
       for any learning algorithm $A$ and $m < |X|/2$,
       there exists a distribution $\mathcal{D}$ on $X\times \mathbb{B}$
       and a predictor $f$ such that
       \begin{itemize}
         \item $\mathcal{L}_{\mathcal{D}}(f) = 0$, and
         \item $\displaystyle \mathop{\mathrm{P}}_{S\sim \mathcal{D}^m}\left(\mathcal{L}_{\mathcal{D}}(A(S)) > \frac{1}{8}\right) \geq \frac{1}{7}$.
       \end{itemize}\<close>
       
theorem no_free_lunch_ML:
  fixes X :: "'a measure" and m :: nat
    and A :: "(nat \<Rightarrow> 'a \<times> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes X1:"finite (space X) \<Longrightarrow> 2 * m < card (space X)"
    and X2[measurable]:"\<And>x. x \<in> space X \<Longrightarrow> {x} \<in> sets X"
    and m[arith]:"0 < m"
    and A[measurable]: "(\<lambda>(s,x). A s x) \<in> (PiM {..<m} (\<lambda>i. X \<Otimes>\<^sub>M count_space (UNIV :: bool set))) \<Otimes>\<^sub>M X
                                            \<rightarrow>\<^sub>M count_space (UNIV :: bool set)"
  shows "\<exists>\<D> :: ('a \<times> bool) measure. sets \<D> = sets (X \<Otimes>\<^sub>M count_space (UNIV :: bool set)) \<and>
                                     prob_space \<D> \<and>
            (\<exists>f. f \<in> X \<rightarrow>\<^sub>M count_space (UNIV :: bool set) \<and> \<P>((x, y) in \<D>. f x \<noteq> y) = 0) \<and>
            \<P>(s in Pi\<^sub>M {..<m} (\<lambda>i. \<D>). \<P>((x, y) in \<D>. A s x \<noteq> y) > 1 / 8) \<ge> 1 / 7"
proof -
  let ?B = "count_space (UNIV :: bool set)"
  let ?B' = "UNIV :: bool set"
  let ?L = "\<lambda>D f. \<P>((x, y) in D. f x = (\<not> y))"
  have XB[measurable]: "xy \<in> space (X \<Otimes>\<^sub>M ?B) \<Longrightarrow> {xy} \<in> sets (X \<Otimes>\<^sub>M ?B)" for xy
    by (auto simp: space_pair_measure sets_Pair)
  have "space X \<noteq> {}"
    using X1 by force
  have "\<exists>C\<subseteq>space X. finite C \<and> card C = 2 * m"
    by (meson X1 infinite_arbitrarily_large obtain_subset_with_card_n order_less_le)
  then obtain C where C: "C \<subseteq> space X" "finite C" "card C = 2 * m"
    by blast
  have C_ne:"C \<noteq> {}"
    using C assms by force
  have C_sets[measurable]:"C \<in> sets X"
    using C by(auto intro!: sets.countable[OF X2 countable_finite])
  have meas[measurable]:"{(x, y). (x, y) \<in> space (X \<Otimes>\<^sub>M ?B) \<and> g x = (\<not> y)} \<in> sets (X \<Otimes>\<^sub>M ?B)"
    if g[measurable]: "g \<in> X \<rightarrow>\<^sub>M ?B" for g
  proof -
    have "{(x, y). (x, y) \<in> space (X \<Otimes>\<^sub>M ?B) \<and> g x = (\<not> y)}
           = (g -` {True} \<inter> space X) \<times> {False} \<union> (g -` {False} \<inter> space X) \<times> {True}"
      by(auto simp: space_pair_measure)
    also have "... \<in> sets (X \<Otimes>\<^sub>M ?B)"
      by simp
    finally show ?thesis .
  qed

  define fn where "fn \<equiv> from_nat_into (C \<rightarrow>\<^sub>E (UNIV :: bool set))"
  define Dn where "Dn \<equiv> (\<lambda>n. measure_of (space (X \<Otimes>\<^sub>M ?B)) (sets (X \<Otimes>\<^sub>M ?B))
                                         (\<lambda>U. real (card ((SIGMA x:C. {fn n x}) \<inter> U)) / real (card C)))"

  have fn_PiE:"n < card (C \<rightarrow>\<^sub>E ?B') \<Longrightarrow> fn n \<in> C \<rightarrow>\<^sub>E ?B'" for n
    by (simp add: PiE_eq_empty_iff fn_def from_nat_into)
  have ex_n:"f \<in> C \<rightarrow>\<^sub>E ?B' \<Longrightarrow> \<exists>n < card (C \<rightarrow>\<^sub>E ?B'). f = fn n" for f
    using bij_betw_from_nat_into_finite[OF finite_PiE[OF C(2),of "\<lambda>i. ?B'"]]
    by(auto simp: bij_betw_def fn_def)
  have fn_inj: "n < card (C \<rightarrow>\<^sub>E ?B') \<Longrightarrow> n' < card (C \<rightarrow>\<^sub>E ?B') \<Longrightarrow> (\<And>x. x \<in> C \<Longrightarrow> fn n x = fn n' x) \<Longrightarrow> n = n'" for n n'
    using bij_betw_from_nat_into_finite[OF finite_PiE[OF C(2),of "\<lambda>i. ?B'"]] PiE_ext[OF fn_PiE[of n] fn_PiE[of n']]
    by(auto simp: bij_betw_def fn_def inj_on_def)

  have fn_meas[measurable]:"fn n \<in> X \<rightarrow>\<^sub>M ?B" for n
  proof -
    have "countable (C \<rightarrow>\<^sub>E (UNIV :: bool set))"
      using C by(auto intro!: countable_PiE)
    hence "fn n \<in> C \<rightarrow>\<^sub>E (UNIV :: bool set)"
      by (simp add: PiE_eq_empty_iff fn_def from_nat_into)
    hence "fn n = (\<lambda>x. if x \<in> C then fn n x else undefined)"
      by auto
    also have "... \<in> X \<rightarrow>\<^sub>M ?B"
    proof(subst measurable_restrict_space_iff[symmetric])
      have "sets (restrict_space X C) = Pow C"
        using X2 C by(intro sets_eq_countable) (auto simp: countable_finite sets_restrict_space_iff)
      thus "fn n \<in> restrict_space X C \<rightarrow>\<^sub>M ?B"
        by (simp add: Measurable.pred_def assms(1))
    qed auto
    finally show ?thesis .
  qed

  have sets_Dn[measurable_cong]: "\<And>n. sets (Dn n) = sets (X \<Otimes>\<^sub>M ?B)"
    and space_Dn:"\<And>n. space (Dn n) = space (X \<Otimes>\<^sub>M ?B)"
    by(simp_all add: Dn_def)
  have emeasure_Dn: "emeasure (Dn n) U = ennreal (real (card ((SIGMA x:C. {fn n x}) \<inter> U)) / real (card C))"
    (is "_ = ennreal (?\<mu> U)")
    if U[measurable]:"U \<in> X \<Otimes>\<^sub>M ?B" for U n
  proof(rule emeasure_measure_of[where \<Omega>="space (X \<Otimes>\<^sub>M ?B)" and A="sets (X \<Otimes>\<^sub>M ?B)"])
    let ?\<mu>' = "\<lambda>U. ennreal (?\<mu> U)"
    show "countably_additive (sets (Dn n)) ?\<mu>'"
      unfolding countably_additive_def
    proof safe
      fix Ui :: "nat \<Rightarrow> _ set"
      assume Ui:"range Ui \<subseteq> sets (Dn n)" "disjoint_family Ui"
      have fin: "finite {i. (SIGMA x:C. {fn n x}) \<inter> Ui i \<noteq> {}}" (is "finite ?I")
      proof(rule ccontr)
        assume "infinite {i. (SIGMA x:C. {fn n x}) \<inter> Ui i \<noteq> {}}"
        with Ui(2)
        have "infinite (\<Union> ((\<lambda>i. (SIGMA x:C. {fn n x}) \<inter> Ui i) ` {i.  (SIGMA x:C. {fn n x}) \<inter> Ui i \<noteq> {}}))"
          (is "infinite ?\<U>")
          by(intro infinite_disjoint_family_imp_infinite_UNION) (auto simp: disjoint_family_on_def)
        moreover have "?\<U> \<subseteq> (SIGMA x:C. {fn n x})"
          by blast
        ultimately have "infinite (SIGMA x:C. {fn n x})"
          by fastforce
        with C(2) show False
          by blast
      qed
      hence sum:"summable (\<lambda>i. ?\<mu> (Ui i))"
        by(intro summable_finite[where N="{i. (SIGMA x:C. {fn n x}) \<inter> Ui i \<noteq> {}}"]) auto
      have "(\<Sum>i. ?\<mu>' (Ui i)) = ennreal (\<Sum>i. ?\<mu> (Ui i))"
        by(intro sum suminf_ennreal2) auto
      also have "... = (\<Sum>i\<in>?I. ?\<mu> (Ui i))"
        by(subst suminf_finite[OF fin]) auto
      also have "... = ?\<mu>' (\<Union> (range Ui))"
      proof -
        have *:"(\<Sum>i\<in>?I. real (card ((SIGMA x:C. {fn n x}) \<inter> Ui i))) = real (\<Sum>i\<in>?I. (card ((SIGMA x:C. {fn n x}) \<inter> Ui i)))"
          by simp
        also have "... = real (card (\<Union> ((\<lambda>i. (SIGMA x:C. {fn n x}) \<inter> Ui i) ` ?I)))"
          using C Ui fin unfolding disjoint_family_on_def
          by(subst card_UN_disjoint) blast+
        also have "... = real (card ((SIGMA x:C. {fn n x}) \<inter> \<Union> (range Ui)))"
          by(rule arg_cong[where f="\<lambda>x. real (card x)"]) blast
        finally show ?thesis
          by(simp add: sum_divide_distrib[symmetric])
      qed
      finally show "(\<Sum>i. ?\<mu>' (Ui i)) = ?\<mu>' (\<Union> (range Ui))" .
    qed
  qed(auto simp: Dn_def positive_def intro!:sets.sets_into_space)
  interpret Dn: prob_space "Dn n" for n
  proof
    have [simp]: "(SIGMA x:C. {fn n x}) \<inter> space (X \<Otimes>\<^sub>M ?B) = (SIGMA x:C. {fn n x})"
      using measurable_space[OF fn_meas] C(1) space_pair_measure by blast
    show "emeasure (Dn n) (space (Dn n)) = 1"
      using C_ne C by(simp add: emeasure_Dn space_Dn)
  qed
  interpret fp: finite_product_prob_space "\<lambda>i. Dn n" "{..<m}" for n
    by standard auto
  have measure_Dn: "measure (Dn n) U = real (card ((SIGMA x:C. {fn n x}) \<inter> U)) / real (card C)"
    if U:"U \<in> X \<Otimes>\<^sub>M ?B" for U n
    using emeasure_Dn[OF U] by(simp add: Dn.emeasure_eq_measure)
  have measure_Dn': "measure (Dn n) U = (\<Sum>x\<in>C. of_bool ((x,fn n x) \<in> U)) / real (card C)"
    if U[measurable]:"U \<in> X \<Otimes>\<^sub>M ?B" for U n
  proof -
    have *:"(SIGMA x:C. {fn n x}) \<inter> U = (SIGMA x:C. {y. y = fn n x \<and> (x,y) \<in> U})"
      by blast
    have "(x,fn n x) \<in> U \<Longrightarrow> {y. y = fn n x \<and> (x, y) \<in> U} = {fn n x}"
      and "(x,fn n x) \<notin> U \<Longrightarrow> {y. y = fn n x \<and> (x, y) \<in> U} = {}" for x
      by blast+
    hence **:"real (card {y. y = fn n x \<and> (x, y) \<in> U}) =  of_bool ((x,fn n x) \<in> U)" for x
      by auto
    show ?thesis
      by(auto simp: measure_Dn * card_SigmaI[OF C(2)] **)
  qed

  let ?LossA = "\<lambda>n s. ?L (Dn n) (A s)"
  have [measurable]: "(\<lambda>s. ?LossA n s) \<in> borel_measurable (PiM {..<m} (\<lambda>i. X \<Otimes>\<^sub>M ?B))" for n
    by measurable (auto simp add: space_Dn)
  have Dn_fn_0:"\<P>((x, y) in Dn n. fn n x \<noteq> y) = 0" for n
  proof -
    have "(SIGMA x:C. {fn n x}) \<inter> {(x, y). (x, y) \<in> space (X \<Otimes>\<^sub>M count_space UNIV) \<and> fn n x = (\<not> y)} = {}"
      by auto
    thus ?thesis
      by(simp add: measure_Dn space_Dn)
  qed

  have [measurable]:"(SIGMA x:C. {fn n x}) \<in> sets (X \<Otimes>\<^sub>M count_space UNIV)" for n
    by(rule sets.countable) (use C in "auto intro!: sets_Pair X2 C(1) countable_finite")
  have integ[simp]:"integrable (PiM {..<m} (\<lambda>i. Dn n)) (\<lambda>s. ?LossA n s)" for n
    by(auto intro!: fp.P.integrable_const_bound[where B=1])

  have [measurable]:"{xn} \<in> sets (Pi\<^sub>M {..<m} (\<lambda>i. X \<Otimes>\<^sub>M ?B))"
    and fp_prob:"fp.prob n {xn} = 1 / real (card C) ^ m"
    if h:"xn \<in> {..<m} \<rightarrow>\<^sub>E (SIGMA x:C. {fn n x})" for xn n
  proof -
    have [simp]: "i < m \<Longrightarrow> xn i \<in> space (X \<Otimes>\<^sub>M ?B)" for i
      using h C(1) by(fastforce simp: PiE_def space_pair_measure Pi_def)
    have *:"{xn} = (\<Pi>\<^sub>E i\<in>{..<m}. {xn i})"
    proof safe
      show "\<And>x. x \<in> (\<Pi>\<^sub>E i\<in>{..<m}. {xn i}) \<Longrightarrow> x = xn"
        by standard (metis PiE_E singletonD h)
    qed(use h in auto)
    also have "... \<in> sets (Pi\<^sub>M {..<m} (\<lambda>i. X \<Otimes>\<^sub>M ?B))"
      by measurable
    finally show "{xn} \<in> sets (Pi\<^sub>M {..<m} (\<lambda>i. X \<Otimes>\<^sub>M ?B))" .
    have "fp.prob n (\<Pi>\<^sub>E i\<in>{..<m}. {xn i}) = (\<Prod>i<m. Dn.prob n {xn i})"
      using h by(intro fp.finite_measure_PiM_emb) simp
    also have "... = (1 / real (card C) ^m) "
    proof -
      have "\<And>i. i < m \<Longrightarrow> ((SIGMA x:C. {fn n x}) \<inter> {xn i}) = {xn i}"
        using h by blast
      thus ?thesis
        by(simp add: measure_Dn power_one_over)
    qed
    finally show "fp.prob n {xn} = 1 / real (card C) ^ m"
      using * by simp
  qed

 (* Expectation of the loss function w.r.t. Dn^n 
    Equation (5.3) in the textbook. *)
  have exp_eq:"(\<integral>s. ?LossA n s \<partial>(PiM {..<m} (\<lambda>i. Dn n))) = (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C. ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card C) ^ m" for n
  proof -
    have "(\<integral>s. ?LossA n s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))
           = (\<integral>s. ?LossA n s * indicat_real (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x}))) s
           + ?LossA n s * indicat_real (space (PiM {..<m} (\<lambda>i. Dn n)) - (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x})))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))"
      by(auto intro!: Bochner_Integration.integral_cong simp: indicator_def)
    also have "... = (\<integral>s. ?LossA n s * indicat_real (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x}))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))
                   + (\<integral>s. ?LossA n s * indicat_real (space (PiM {..<m} (\<lambda>i. Dn n)) - (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x})))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))"
      by(rule Bochner_Integration.integral_add)
        (auto intro!: fp.P.integrable_const_bound[where B=1] simp: mult_le_one)
    also have "... = (\<integral>s. ?LossA n s * indicat_real (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x}))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))"
    proof -
      have *:"(\<integral>s. ?LossA n s * indicat_real (space (PiM {..<m} (\<lambda>i. Dn n)) - (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x})))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n))) \<ge> 0"
        by simp
      have "(\<integral>s. ?LossA n s * indicat_real (space (PiM {..<m} (\<lambda>i. Dn n)) - (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x})))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))
            \<le> (\<integral>s. indicat_real (space (PiM {..<m} (\<lambda>i. Dn n)) - (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x})))) s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))"
        by(intro integral_mono) (auto intro!: fp.P.integrable_const_bound[where B=1] simp: mult_le_one indicator_def)
      also have "... = 1 - fp.prob n (PiE {..<m} (\<lambda>i. (SIGMA x:C. {fn n x})))"
        by(simp add: fp.P.prob_compl)
      also have "... = 0"
        using C by(simp add: fp.finite_measure_PiM_emb measure_Dn )
      finally show ?thesis
        using * by simp
    qed
    also have "... = (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E (SIGMA x:C. {fn n x}). ?LossA n s * fp.prob n {s})"
      using C by(auto intro!: integral_indicator_finite_real finite_PiE le_neq_trans)
    also have "... = (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E (SIGMA x:C. {fn n x}). ?LossA n s) / real (card C) ^ m"
      by(simp add: fp_prob sum_divide_distrib)
    also have "... = (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C. ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card C) ^ m"
    proof -
      have *:"{..<m} \<rightarrow>\<^sub>E (SIGMA x:C. {fn n x}) = (\<lambda>s. \<lambda>i\<in>{..<m}. (s i, fn n (s i))) ` ({..<m} \<rightarrow>\<^sub>E C)"
        unfolding set_eq_iff
      proof safe
        show "s \<in> {..<m} \<rightarrow>\<^sub>E (SIGMA x:C. {fn n x}) \<Longrightarrow> s \<in> (\<lambda>s. \<lambda>i\<in>{..<m}. (s i, fn n (s i))) ` ({..<m} \<rightarrow>\<^sub>E C)" for s
          by(intro rev_image_eqI[where b=s and x="\<lambda>i\<in>{..<m}. fst (s i)"]) (force simp: PiE_def Pi_def extensional_def)+
      qed auto
      have **:"inj_on (\<lambda>s. \<lambda>i\<in>{..<m}. (s i, fn n (s i))) ({..<m} \<rightarrow>\<^sub>E C)"
        by(intro inj_onI) (metis (mono_tags, lifting) PiE_ext prod.simps(1) restrict_apply')
      show ?thesis
        by(subst sum.reindex[where A="{..<m} \<rightarrow>\<^sub>E C" and h="\<lambda>s. \<lambda>i\<in>{..<m}. (s i, fn n (s i))",simplified,symmetric])
          (use * ** in auto) 
    qed
    finally show ?thesis .
  qed

  have eqL:"?L (Dn n) h = (\<Sum>x\<in>C. of_bool (h x = (\<not> fn n x))) / real (card C)" if h[measurable]:"h \<in> X \<rightarrow>\<^sub>M ?B" for n h
  proof -
    have "?L (Dn n) h = (\<Sum>x\<in>C. of_bool ((x, fn n x) \<in> space (X \<Otimes>\<^sub>M ?B) \<and> h x = (\<not> fn n x))) / real (card C)"
      by(simp add: space_Dn measure_Dn')
    also have "... =  (\<Sum>x\<in>C. of_bool (h x = (\<not> fn n x))) / real (card C)"
      using C by(auto simp: space_pair_measure Collect_conj_eq Int_assoc[symmetric])
    finally show ?thesis .
  qed

  have nz1[arith]:"real (card (C \<rightarrow>\<^sub>E ?B')) > 0" "real (card C) > 0" "0 < real (card ({..<m} \<rightarrow>\<^sub>E C))"
    using C(2) C_ne by(simp_all add: card_funcsetE card_gt_0_iff)

  have ne:"finite ((\<lambda>n. fp.expectation n
            (\<lambda>s. Dn.prob n {(x, y). (x, y) \<in> space (Dn n) \<and> A s x = (\<not> y)})) ` {..<card (C \<rightarrow>\<^sub>E ?B')})"
          "((\<lambda>n. fp.expectation n
            (\<lambda>s. Dn.prob n {(x, y). (x, y) \<in> space (Dn n) \<and> A s x = (\<not> y)})) ` {..<card (C \<rightarrow>\<^sub>E ?B')}) \<noteq> {}" (is ?ne)
  proof -
    have "0 < card (C \<rightarrow>\<^sub>E ?B')"
      using C_ne C(2) by(auto simp: card_gt_0_iff finite_PiE)
    thus ?ne
      by blast
  qed simp
  (* Equation (5.1) in the textbook *)
  have max_geq_q:"(MAX n\<in>{..<card (C \<rightarrow>\<^sub>E ?B')}. (\<integral>s. ?LossA n s \<partial>(PiM {..<m} (\<lambda>i. Dn n)))) \<ge> 1 / 4" (is "_ \<le> ?Max")
  proof -

    (* Equation (5.4) in the textbook *)
    have "(MIN s\<in>{..<m} \<rightarrow>\<^sub>E C. (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card (C \<rightarrow>\<^sub>E ?B')))
          \<le> ?Max" (is "?Min1 \<le> _")
    proof -
      have "?Min1
           \<le> (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C.
                (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B').
                      ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card (C \<rightarrow>\<^sub>E ?B'))) / real (card ({..<m} \<rightarrow>\<^sub>E C))"
      proof(subst pos_le_divide_eq)
        show "?Min1 * real (card ({..<m} \<rightarrow>\<^sub>E C))
            \<le> (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C. (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card (C \<rightarrow>\<^sub>E ?B')))"
          using C by(simp add: mult.commute) (auto intro!: finite_PiE card_Min_le_sum_of_nat)
      qed fact
      also have "...
            = (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C.
                 (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B').
                       ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card (C \<rightarrow>\<^sub>E ?B'))) / real (card C) ^ m"
        by(simp add: card_PiE)
      also have "...
               = (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B').
                   (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C.
                      ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card C) ^ m) / real (card (C \<rightarrow>\<^sub>E ?B'))"
        unfolding sum_divide_distrib[symmetric] by(subst sum.swap) simp
      also have "... \<le> ?Max"
      proof -
        have "real (card (C \<rightarrow>\<^sub>E ?B')) * ?Max
            = real (card (C \<rightarrow>\<^sub>E ?B'))
            * (MAX n\<in>{..<card (C \<rightarrow>\<^sub>E ?B')}. (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C. ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card C) ^ m)"
          by (simp add: exp_eq)
        also have "... \<ge> (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). (\<Sum>s\<in>{..<m} \<rightarrow>\<^sub>E C. ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card C) ^ m)"
          using sum_le_card_Max_of_nat[of "{..<card (C \<rightarrow>\<^sub>E ?B')}"] finite_PiE[OF C(2)] by auto
        finally show ?thesis
          by(subst pos_divide_le_eq) (simp, argo)
      qed
      finally show ?thesis .
    qed

    (* Equation (5.6) *)
    have "1 / 4 \<le> ?Min1"
    proof(safe intro!: Min_ge_iff[THEN iffD2])
      fix s
      assume s: "s \<in> {..<m} \<rightarrow>\<^sub>E C"
      hence [measurable]: "(\<lambda>i\<in>{..<m}. (s i, fn n (s i))) \<in> space (PiM {..<m} (\<lambda>i. X \<Otimes>\<^sub>M ?B))" for n
        using C by(auto simp: space_PiM space_pair_measure)
      let ?V = "C - (s ` {..<m})"
      have fin_V:"finite ?V"
        using C by blast
      have cardV: "card ?V \<ge> m"
      proof -
        have "card (s ` {..<m}) \<le> m"
          by (metis card_image_le card_lessThan finite_lessThan)
        hence "m \<le> card C - card (s ` {..<m})"
          using C(3) by simp
        also have "card C - card (s ` {..<m}) \<le> card ?V"
          by(rule diff_card_le_card_Diff) simp
        finally show ?thesis .
      qed
      hence V_ne: "?V \<noteq> {}" "card ?V > 0"
        using m by force+
      have "(1 / 2) * (1 / 2)
          = (1 / 2)
          * (MIN v\<in>?V. (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v))) / real (card (C \<rightarrow>\<^sub>E ?B')))"
      proof(rule arg_cong[where f="(*) (1 / 2)"])
        have "(\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v))) / real (card (C \<rightarrow>\<^sub>E ?B')) = 1 / 2"
            if v:"v \<in> ?V" for v
        proof -
          define B where "B \<equiv> {(n, n')|n n'. n < card (C \<rightarrow>\<^sub>E ?B') \<and> fn n v = False \<and> n' < card (C \<rightarrow>\<^sub>E ?B')
                                              \<and> fn n' v = True \<and> (\<forall>x\<in>C - {v}. fn n x = fn n' x)}"
          have B1:"fst ` B \<union> snd ` B = {..<card (C \<rightarrow>\<^sub>E ?B')}"
          proof -
            have "n \<in> fst ` B \<union> snd ` B" if n:"n < card (C \<rightarrow>\<^sub>E ?B')" for n
            proof(cases "fn n v = True")
              assume h:"fn n v = True"
              let ?fn' = "\<lambda>x. if x = v then False else fn n x"
              have fn':"\<And>x. x \<noteq> v \<Longrightarrow> fn n x = ?fn' x" "?fn' v = False"
                by auto
              hence fn'1:"?fn' \<in> C \<rightarrow>\<^sub>E ?B'"
                using fn_PiE[OF n] v by auto
              then obtain n' where n': "n' < card (C \<rightarrow>\<^sub>E ?B')" "fn n' = ?fn'"
                using ex_n by (metis (lifting))
              hence "(n',n) \<in> B"
                using n' fn'1 fn_PiE[OF n] n h fn' by(auto simp: B_def)
              thus ?thesis
                by force
            next
              assume h:"fn n v \<noteq> True"
              let ?fn' = "\<lambda>x. if x = v then True else fn n x"
              have fn':"\<And>x. x \<noteq> v \<Longrightarrow> fn n x = ?fn' x" "?fn' v = True"
                by auto
              hence fn'1:"?fn' \<in> C \<rightarrow>\<^sub>E ?B'"
                using fn_PiE[OF n] v by auto
              then obtain n' where n': "n' < card (C \<rightarrow>\<^sub>E ?B')" "fn n' = ?fn'"
                using ex_n by (metis (lifting))
              hence "(n,n') \<in> B"
                using n' fn'1 fn_PiE[OF n] n h fn' by(auto simp: B_def)
              thus ?thesis
                by force
            qed
            moreover have "\<And>n. n \<in> fst ` B \<union> snd ` B \<Longrightarrow> n < card (C \<rightarrow>\<^sub>E ?B')"
              by(auto simp: B_def)
            ultimately show ?thesis
              by blast
          qed
          have B2:"fst ` B \<inter> snd ` B = {}"
            by(auto simp: B_def)
          have B3: "inj_on fst B"
            by(auto intro!: fn_inj inj_onI simp: B_def)
          have B4: "inj_on snd B"
            by(fastforce intro!: fn_inj inj_onI simp: B_def)
          have B5:"of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v
                   = (\<not> fn n v)) + of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n' (s i))) v = (\<not> fn n' v)) = (1 :: real)"
            if nn':"(n,n') \<in> B" for n n'
          proof -
            have "(\<lambda>i\<in>{..<m}. (s i, fn n (s i))) = (\<lambda>i\<in>{..<m}. (s i, fn n' (s i)))"
              by standard (use s nn' v in "auto simp: B_def")
            thus ?thesis
              using nn' by(auto simp: B_def)
          qed
          have "(\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v)))
                 = 1 * real (card {..<card (C \<rightarrow>\<^sub>E ?B')}) / 2"
            by(intro sum_of_const_pairs[where B=B] B1 B2 B3 B4 B5) simp
          thus ?thesis
            by simp
        qed
        thus "1 / 2 = (MIN v\<in>?V. (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v))) / real (card (C \<rightarrow>\<^sub>E ?B')))"
          by (metis (mono_tags, lifting) V_ne(1) fin_V obtains_MIN)        
      qed
      also have "...
              \<le> (1 / 2)
               * ((\<Sum>v\<in>?V. (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v)))
                             / real (card (C \<rightarrow>\<^sub>E ?B')))
                   / real (card ?V))"
        using V_ne by(intro mult_le_cancel_left_pos[THEN iffD2] pos_le_divide_eq[THEN iffD2])
                     (simp_all add: Groups.mult_ac(2) card_Min_le_sum_of_nat fin_V)
      also have "...
              = (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). ((\<Sum>v\<in>?V. of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v)))
                                         / (2 * real (card ?V))) / real (card (C \<rightarrow>\<^sub>E ?B')))"
        unfolding sum_divide_distrib[symmetric] by(subst sum.swap) simp
      also have "... \<le> (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) / real (card (C \<rightarrow>\<^sub>E ?B')))"
      proof(safe intro!: sum_mono divide_right_mono)
        fix n
        have "(\<Sum>v\<in>?V. of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v))) / (2 * real (card ?V))
              \<le> (\<Sum>v\<in>?V. of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v))) / real (card C)"
          using cardV by(auto simp: C(3) intro!: divide_left_mono sum_nonneg)
        also have "... \<le> (\<Sum>x\<in>C. of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) x = (\<not> fn n x))) / real (card C)"
          using C by(intro sum_mono2 divide_right_mono) auto
        also have "... = ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))"
          by(simp add: eqL)
        finally show "(\<Sum>v\<in>?V. of_bool (A (\<lambda>i\<in>{..<m}. (s i, fn n (s i))) v = (\<not> fn n v))) / (2 * real (card ?V))
                      \<le> ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))" .
      qed simp
      finally show "1 / 4 \<le> (\<Sum>n<card (C \<rightarrow>\<^sub>E ?B'). ?LossA n (\<lambda>i\<in>{..<m}. (s i, fn n (s i)))) / real (card (C \<rightarrow>\<^sub>E ?B'))"
        by(simp add: sum_divide_distrib)
    qed(use m C in "auto intro!: finite_PiE simp: PiE_eq_empty_iff")
    also have "... \<le> ?Max"
      by fact
    finally show ?thesis .
  qed
 
  hence "\<exists>n. n < card (C \<rightarrow>\<^sub>E ?B') \<and> (\<integral>s. ?LossA n s \<partial>(PiM {..<m} (\<lambda>i. Dn n))) \<ge> 1 / 4"
    using Max_ge_iff[OF ne] by blast
  then obtain n where n:"n < card (C \<rightarrow>\<^sub>E ?B')" "(\<integral>s. ?LossA n s \<partial>(PiM {..<m} (\<lambda>i. Dn n))) \<ge> 1 / 4"
    by blast
 
  have "1 / 7 \<le> ((\<integral>s. ?LossA n s \<partial>(PiM {..<m} (\<lambda>i. Dn n))) - (1 - 7/ 8)) / (7 / 8)"
    using n by argo
  also have "... \<le> \<P>(s in Pi\<^sub>M {..<m} (\<lambda>i. Dn n). \<P>((x, y) in Dn n. A s x = (\<not> y)) > 1 - 7 / 8)"
    by(intro fp.Markov_inequality_measure_minus) auto
  also have "... = \<P>(s in Pi\<^sub>M {..<m} (\<lambda>i. Dn n). \<P>((x, y) in Dn n. A s x = (\<not> y)) > 1 / 8)"
    by simp
  finally have "1 / 7 \<le> \<P>(s in Pi\<^sub>M {..<m} (\<lambda>i. Dn n). \<P>((x, y) in Dn n. A s x = (\<not> y)) > 1 / 8)" .
  thus ?thesis
    using Dn_fn_0[of n]
    by(auto intro!: exI[where x="Dn n"] exI[where x="fn n"] simp: sets_Dn Dn.prob_space_axioms)
qed

end