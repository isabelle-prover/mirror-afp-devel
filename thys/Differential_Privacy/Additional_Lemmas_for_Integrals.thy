(*
 Title:Additional_Lemmas_for_Integrals.thy
 Author: Tetsuya Sato
 Author: Yasuhiko Minamide
*)

theory Additional_Lemmas_for_Integrals
  imports"HOL-Probability.Probability"
begin

section \<open>Lemmas for Integrals\<close>

subsection \<open>Lemmas on Nonnegative Integrals\<close>

(*
 The below lemma is for integrals on intervals of type {.. a}.
 It is a modification of Equivalence_Lebesgue_Henstock_Integration.nn_integral_FTC_atLeast,
 which is for integrals on intervals of type {a ..}. The proof is also borrowed from it.
*)

lemma nn_integral_FTC_atGreatest:
  fixes f :: "real \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. x \<le> a \<Longrightarrow> DERIV F x :> f x"
  assumes nonneg: "\<And>x. x \<le> a \<Longrightarrow> 0 \<le> f x"
  assumes lim: "(F \<longlongrightarrow> T) at_bot"
  shows "(\<integral>\<^sup>+x. ennreal (f x) * indicator {..a} x \<partial>lborel) = F a - T"
proof-
  let ?f ="\<lambda>(i :: nat) (x :: real). ennreal (f x) * indicator {(a - real i)..a} x"
  let ?fR ="\<lambda>x. ennreal (f x) * indicator {.. a} x"

  have F_mono: "x \<le> a \<Longrightarrow> y \<le> x \<Longrightarrow> F y \<le> F x"for x y
    using f nonneg by (intro DERIV_nonneg_imp_nondecreasing[of y x F]) (auto intro: order_trans)
  hence F_le_T: "x \<le> a \<Longrightarrow> T \<le> F x"for x
    by (intro tendsto_upperbound[OF lim]) (auto simp: eventually_at_bot_linorder)
  have "(SUP i. ?f i x) = ?fR x"for x
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    obtain n where"a - x < real n"
      using reals_Archimedean2[of"a - x"] ..
    hence "eventually (\<lambda>n. ?f n x = ?fR x) sequentially"
      by (auto intro!: eventually_sequentiallyI[where c=n] split: split_indicator)
    thus"(\<lambda>n. ?f n x) \<longlonglongrightarrow> ?fR x"
      by (rule tendsto_eventually)
  qed (auto simp: nonneg incseq_def le_fun_def split: split_indicator)
  hence "integral\<^sup>N lborel ?fR = (\<integral>\<^sup>+ x. (SUP i. ?f i x) \<partial>lborel)"
    by auto
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. ?f i x \<partial>lborel))"
  proof (rule nn_integral_monotone_convergence_SUP)
    show "incseq ?f"
      using nonneg by (auto simp: incseq_def le_fun_def split: split_indicator)
    show "\<And>i. (?f i) \<in> borel_measurable lborel"
      using f_borel by auto
  qed
  also have "\<dots> = (SUP i. ennreal (F a - F (a - real i)))"
    by (subst nn_integral_FTC_Icc[OF f_borel f nonneg]) auto
  also have "\<dots> = F a - T"
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    show "incseq (\<lambda>i. ennreal (F a - F (a - real i)))"
      by (auto simp: incseq_def intro!: ennreal_le_iff[THEN iffD2] F_mono)
    have P: "LIM x sequentially. a - real x :> at_bot"
    proof(subst filterlim_at_bot_lt[where c = 0],safe)
      fix Z :: real assume "Z < 0"
      show "\<forall>\<^sub>F x in sequentially. a - real x \<le> Z"
      proof (rule eventually_sequentiallyI[where c ="nat \<lfloor>(a - Z)\<rfloor> + 1"])
        fix x assume "nat \<lfloor>a - Z\<rfloor> + 1 \<le> x"
        show "a - real x \<le> Z"
          using \<open>nat \<lfloor>a - Z\<rfloor> + 1 \<le> x\<close> by linarith
      qed
    qed
    have "(\<lambda>x. F (a - real x)) \<longlonglongrightarrow> T"
      by(intro filterlim_compose[OF lim P])
    thus"(\<lambda>i. ennreal (F a - F (a - real i))) \<longlonglongrightarrow> ennreal (F a - T)"
      by (auto simp: F_mono F_le_T tendsto_diff)
  qed
  finally show ?thesis by auto
qed

lemma nn_integral_split_null_intersection:
  assumes [measurable]: "f \<in> borel_measurable M"
    "B \<in> sets M" "C \<in> sets M"
    "B \<inter> C \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
proof-
  let ?D ="B \<inter> C"
  have eq1: "(\<integral>\<^sup>+x \<in> B. f x \<partial>M) = (\<integral>\<^sup>+x \<in> (B - ?D). f x \<partial>M)"
  proof(rule nn_integral_null_delta)
    have "sym_diff B (B - ?D) = ?D"by auto
    thus"sym_diff B (B - ?D)\<in> null_sets M"using assms by auto
  qed(auto)
  have "B \<union> C = (B - ?D) \<union> C"by auto
  hence "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> (B - ?D) \<union> C. f x \<partial>M)"
    by auto
  also have "... =(\<integral>\<^sup>+x \<in> (B - ?D). f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
    by(rule nn_integral_disjoint_pair,auto)
  thus ?thesis using eq1 calculation by auto
qed

lemma nn_integral_split_null_intersection2:
  assumes [measurable]: "f \<in> borel_measurable M"
    "B \<in> sets M" "C \<in> sets M"
    "B \<inter> C \<in> null_sets M"
    "A = B \<union> C"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
  by (auto simp: assms(4) assms(5) nn_integral_split_null_intersection)

lemma nn_integral_interval_lessThan_atMost:
  fixes m :: "real"
  assumes "f \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+ x\<in> {..m}. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {..<m}. f x \<partial>lborel)"
proof(rule nn_integral_null_delta)
  have "sym_diff {..m} {..<m} = {m}"by auto
  also have "... \<in> null_sets lborel"
    by auto
  finally show "sym_diff {..m} {..<m} \<in> null_sets lborel".
qed(auto)

lemma nn_integral_interval_greaterThan_atLeast:
  fixes m :: "real"
  assumes "f \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+ x\<in> {m..}. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {m<..}. f x \<partial>lborel)"
proof(rule nn_integral_null_delta)
  have "sym_diff {m..} {m<..} = {m}"by auto
  also have "... \<in> null_sets lborel"
    by auto
  finally show "sym_diff {m..} {m<..} \<in> null_sets lborel".
qed(auto)

lemma nn_set_integral_lborel_split:
  fixes m :: "real"
  assumes [measurable]: "f \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+ x\<in>UNIV. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {..m}. f x \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {m..}. f x \<partial>lborel)"
proof(rule nn_integral_split_null_intersection2)
  have "{..m} \<inter> {m..} = {m}"by auto
  thus"{..m} \<inter> {m..} \<in> null_sets lborel"by auto
qed(auto)

lemma nn_set_integral_lborel_split_AtMost:
  fixes m n :: "real"
  assumes [measurable]: "f \<in> borel_measurable lborel"
    and "n \<le> m"
  shows "(\<integral>\<^sup>+ x\<in>{..m}. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {..n}. f x \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {n..m}. f x \<partial>lborel)"
proof(rule nn_integral_split_null_intersection2)
  show "{..m} = {..n} \<union> {n..m}"using assms(2) by auto
qed(auto simp add: assms(2))

lemma nn_set_integral_lborel_split_AtLeast:
  fixes m n :: "real"
  assumes [measurable]: "f \<in> borel_measurable lborel"
    and "n \<le> m"
  shows "(\<integral>\<^sup>+ x\<in>{n..}. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {n..m}. f x \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {m..}. f x \<partial>lborel)"
proof(rule nn_integral_split_null_intersection2)
  show "{n..} = {n..m} \<union> {m..}"using assms(2) by auto
qed(auto simp add: assms(2))

lemma nn_set_integral_lborel_split_AtMostAtLeast:
  fixes l m n :: "real"
  assumes [measurable]: "f \<in> borel_measurable lborel"
    and "l \<le> m"
    and "m \<le> n"
  shows "(\<integral>\<^sup>+ x\<in>{l..n}. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {l..m}. f x \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {m..n}. f x \<partial>lborel)"
proof(rule nn_integral_split_null_intersection2, auto simp: assms(2,3))
  show "\<And>x. l \<le> x \<Longrightarrow> x \<le> m \<Longrightarrow> x \<le> n"using assms(2,3) by auto
  show "\<And>x. m \<le> x \<Longrightarrow> x \<le> n \<Longrightarrow> l \<le> x"using assms(2,3) by auto
qed

lemma nn_integral_lborel_split:
  fixes m :: "real"
  assumes [measurable]: "f \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+ x. f x \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {..m}. f x \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {m..}. f x \<partial>lborel)"
  using nn_set_integral_lborel_split by force

subsection \<open>Lemmas on Bochner Integrals\<close>

lemma integral_split_indicator[simp]:
  assumes "\<Omega> \<in> sets M" "(f :: _\<Rightarrow> real) \<in> borel_measurable M" "integrable M f"
  shows "(\<integral> x. f x \<partial>M) = (\<integral> x \<in> \<Omega>. f x \<partial>M) + (\<integral> x \<in> space M - \<Omega>. f x \<partial>M)"
proof -
  have "(\<Omega> \<union> (space M - \<Omega>)) = space M"
    using assms(1) sets.sets_into_space by blast
  hence "(\<integral> x. f x \<partial>M) = (\<integral> x\<in> (\<Omega> \<union> (space M - \<Omega>)). f x \<partial>M)"
    by (auto simp: assms(3) set_integral_space)
  also have "... =(\<integral> x \<in> \<Omega>. f x \<partial>M) + (\<integral> x \<in> space M - \<Omega>. f x \<partial>M)"
  proof(rule set_integral_Un)
    have P: "set_integrable M (space M) f"unfolding set_integrable_def
      using integrable_mult_indicator assms by blast
    thus"set_integrable M \<Omega> f"using set_integrable_subset assms sets.sets_into_space by metis
    have "(space M - \<Omega>) \<in> sets M"
      using assms by auto
    thus"set_integrable M (space M - \<Omega>) f"using P set_integrable_subset sets.sets_into_space by metis
  qed(auto)
  finally show "(\<integral> x. f x \<partial>M) = (\<integral> x \<in> \<Omega>. f x \<partial>M) + (\<integral> x \<in> space M - \<Omega>. f x \<partial>M)".
qed

lemma integral_drop_negative_part:
  assumes "(f :: _\<Rightarrow>real) \<in> borel_measurable M"
    and "integrable M f"
  shows "(\<integral> x. f x \<partial>M) \<le> (\<integral>x\<in>{x \<in> space M. 0 < f x}. f x \<partial>M)"
proof-
  let ?A ="{x \<in> space M. 0 < f x}"
  have PM: "?A \<in> sets M"
    using assms(1) assms(2) borel_measurable_le by auto
  have splitP: "(\<integral> x. f x \<partial>M) = (\<integral> x \<in>?A. f x \<partial>M) + (\<integral> x \<in> space M - ?A. f x \<partial>M)"
    using assms by auto
  have negpart: "\<forall> x\<in> space M.(indicator (space M - ?A) x)* (f x) \<le> 0"
  proof
    fix x assume A: "x \<in> space M"
    show "indicat_real (space M - ?A) x *(f x) \<le> 0"
    proof(cases)
      assume "x \<in> ?A"
      hence "indicat_real (space M - ?A) x = 0"by auto
      thus ?thesis by auto
    next assume A1: "x \<notin> ?A"
      hence "x \<in> space M - ?A"using A by auto
      hence "indicat_real (space M - ?A) x = 1"by auto moreover
      have "f x \<le> 0"using A1 A by auto
      thus ?thesis
        by (auto simp: calculation)
    qed
  qed
  have "(\<integral> x \<in> space M - ?A. f x \<partial>M) \<le> (\<integral> x \<in> space M - ?A. (\<lambda> x.0)x \<partial>M)"
  proof(rule set_integral_mono)
    show "set_integrable M (space M - ?A) f"
      unfolding set_integrable_def
      using assms integrable_mult_indicator sets.compl_sets PM by blast
    show "set_integrable M (space M - ?A) (\<lambda>x. 0)"
      unfolding set_integrable_def
      by auto
    show "\<And>x. x \<in> space M - ?A \<Longrightarrow> f x \<le> 0"
      using negpart by auto
  qed
  also have "... \<le> 0"
    by auto
  finally have ineq0: "(\<integral> x \<in> space M - ?A. f x \<partial>M) \<le> 0".
  show "(\<integral> x. f x \<partial>M) \<le> (\<integral> x \<in>?A. f x \<partial>M)"
    using splitP ineq0 by auto
qed

lemma integral_drop_negative_part2:
  assumes "(f :: _\<Rightarrow>real) \<in> borel_measurable M"
    and "integrable M f"
    and "A \<in> sets M"
    and "{x \<in> space M. 0 < f x} \<subseteq> A"
    and "A \<subseteq> {x \<in> space M. 0 \<le> f x}"
  shows "(\<integral> x. f x \<partial>M) \<le> (\<integral>x \<in> A. f x \<partial>M)"
proof-
  have meas: "A - {x \<in> space M. 0 < f x} \<in> sets M"
    using assms by measurable
  have meas2: "{x \<in> space M. 0 < f x} \<in> sets M"
    using assms by measurable
  have eq0: "\<forall> x \<in> (A - {x \<in> space M. 0 < f x}). f x = 0"
  proof
    fix x assume A: "x \<in> (A - {x \<in> space M. 0 < f x})"
    show "f x = 0"
      using assms A by auto
  qed
  have "(\<integral>x\<in>(A - {x \<in> space M. 0 < f x}). f x \<partial>M) = (\<integral>x\<in>(A - {x \<in> space M. 0 < f x}). (\<lambda> x. 0) x \<partial>M)"
  proof(rule eq0 set_lebesgue_integral_cong)
    show "A - {x \<in> space M. 0 < f x} \<in> sets M"
      using meas by auto
    show "\<forall>x. x \<in> A - {x \<in> space M. 0 < f x} \<longrightarrow> f x = 0"
      using eq0 by blast
  qed
  hence eq1: "(\<integral>x\<in>(A - {x \<in> space M. 0 < f x}). f x \<partial>M) = 0"
    by auto
  have ineq1: "(\<integral> x. f x \<partial>M) \<le> (\<integral>x\<in>{x \<in> space M. 0 < f x}. f x \<partial>M)"
    by(auto intro!: integral_drop_negative_part simp: assms)
  also have "... = (\<integral>x\<in>{x \<in> space M. 0 < f x}. f x \<partial>M) + (\<integral>x\<in>(A - {x \<in> space M. 0 < f x}). f x \<partial>M)"
    using eq1 by auto
  also have "... = (\<integral>x\<in>({x \<in> space M. 0 < f x}\<union>(A - {x \<in> space M. 0 < f x})). f x \<partial>M)"
  proof(rule set_integral_Un[THEN sym])
    show "{x \<in> space M. 0 < f x} \<inter> (A - {x \<in> space M. 0 < f x}) = {}"
      by auto
    have t: "set_integrable M (space M) f"
      unfolding set_integrable_def assms
      using assms(2) integrable_mult_indicator by blast
    show "set_integrable M {x \<in> space M. 0 < f x} f"
      using set_integrable_subset t meas2 by blast
    show "set_integrable M (A - {x \<in> space M. 0 < f x}) f"
      using set_integrable_subset[OF t meas] meas sets.sets_into_space by blast
  qed
  also have "... = (\<integral>x\<in>A. f x \<partial>M)"
    by (auto simp: Un_absorb2 Un_commute assms(4))
  finally show "(\<integral> x. f x \<partial>M) \<le> (\<integral>x\<in>A. f x \<partial>M)".
qed

lemma set_integral_indicator:
	fixes M :: "'a measure" and c :: "real"
	assumes "B \<in> sets M"
	  and "emeasure M B < \<top>"
	shows "(\<integral> x\<in> B. c \<partial>M) = c * measure M B"
proof-
	have "(\<integral> x\<in> B. c \<partial>M) = (\<integral> x. c * indicator B x \<partial>M)"
		by (auto simp: set_lebesgue_integral_def)
	also have "... = c *(\<integral> x. indicator B x \<partial>M)"
		using integral_mult_right_zero by blast
	also have "... = c * measure M B"
	proof-
	  have "(\<integral> x. indicator B x \<partial>M) = measure M B"
	  proof(rule has_bochner_integral_integral_eq,rule has_bochner_integral_real_indicator)
	    show "B \<in> sets M"using assms(1) by auto
	    show "emeasure M B < \<infinity>"using assms(2) by auto
	  qed
	  thus ?thesis by auto
	qed
	finally show "(\<integral> x\<in> B. c \<partial>M) = c * measure M B".
qed

end

