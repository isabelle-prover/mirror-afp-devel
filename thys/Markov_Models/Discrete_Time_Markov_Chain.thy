(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)
header {* Discrete-time Markov chain (i.e. with a finite state space) *}
theory Discrete_Time_Markov_Chain
  imports Discrete_Markov_Kernel
begin

section {* Discrete-Time Markov Chain *}

locale Discrete_Time_Markov_Chain =
  fixes S :: "'s set" and \<tau> :: "'s \<Rightarrow> 's \<Rightarrow> real" and s0 :: "'s"
  assumes finite_S[simp, intro]: "finite S"
    and s0_in_S: "s0 \<in> S"
    and \<tau>_nneg[simp, intro]: "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> 0 \<le> \<tau> s s'"
    and \<tau>_distr: "\<And>s. s \<in> S \<Longrightarrow> (\<Sum>s'\<in>S. \<tau> s s') = 1"
begin

text {*

@{term s} is an arbitrary state which should be in @{term S}, however we do not
enforce this, this simplifies the usage of @{const prob_space} on DTMC.

*}

definition "K s = (if s \<in> S then point_measure S (\<tau> s) else point_measure S (indicator {s0}))"

end

sublocale Discrete_Time_Markov_Chain \<subseteq> K: prob_space "K s" for s
  by default (insert s0_in_S \<tau>_distr K_def, simp add: indicator_def emeasure_point_measure_finite
    space_point_measure one_ereal_def setsum_cases)

sublocale Discrete_Time_Markov_Chain \<subseteq> Discrete_Markov_Kernel S K
  by default (insert finite_S s0_in_S,
    auto intro: countable_finite simp add: K_def sets_point_measure)

context Discrete_Time_Markov_Chain
begin 

lemma nat_case_in_S[intro, simp]: "s \<in> S \<Longrightarrow> \<omega> \<in> UNIV \<rightarrow> S \<Longrightarrow> nat_case s \<omega> i \<in> S"
  by (auto simp: Pi_mem split: nat.split)

lemma E_iff: "s \<in> S \<Longrightarrow> t \<in> S \<Longrightarrow> t \<in> E s \<longleftrightarrow> \<tau> s t \<noteq> 0"
  unfolding E_def by (auto simp: emeasure_point_measure_finite K_def)

lemma E_D: "t \<in> E s \<Longrightarrow> s \<in> S \<Longrightarrow> \<tau> s t \<noteq> 0"
  unfolding E_def by (auto simp: emeasure_point_measure_finite K_def)

lemma E_D': "t \<in> E s \<Longrightarrow> s \<in> S \<Longrightarrow> t \<in> S \<and> \<tau> s t \<noteq> 0"
  using E_iff[of s t] E_D[of t s] by auto

lemma E_eqI: "s \<in> S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (\<And>t. t \<in> S \<Longrightarrow> \<tau> s t \<noteq> 0 \<longleftrightarrow> t \<in> T) \<Longrightarrow> E s = T"
  by (auto intro!: E_iff[THEN iffD2] dest!: E_D')

lemma positive_integral_K:
  fixes f :: "'s \<Rightarrow> ereal"
  assumes [simp]: "s \<in> S" "\<And>t. t \<in> S \<Longrightarrow> 0 \<le> f t"
  shows "(\<integral>\<^isup>+t. f t \<partial>K s) = (\<Sum>t\<in>S. \<tau> s t * f t)"
  by (simp add: positive_integral_point_measure_finite K_def)

lemma integral_K:
  assumes [simp]: "s \<in> S"
  shows "(\<integral>t. f t \<partial>K s) = (\<Sum>t\<in>S. \<tau> s t * f t)"
  by (simp add: lebesgue_integral_point_measure_finite K_def)

lemma measure_K:
  assumes [simp]: "s \<in> S" and A: "A \<subseteq> S"
  shows "measure (K s) A = (\<Sum>t\<in>A. \<tau> s t)"
  using emeasure_point_measure_finite[OF finite_S, of "\<tau> s" A] K.emeasure_eq_measure[of s A] A
  by (auto simp add: subset_eq K_def)

lemma prob_K:
  fixes f :: "'s \<Rightarrow> ereal"
  assumes [simp]: "s \<in> S"
  shows "\<P>(t in K s. P t) = (\<Sum>t\<in>{t\<in>S. P t}. \<tau> s t)"
  using emeasure_point_measure_finite[OF finite_S, of "\<tau> s" "{t\<in>S. P t}"]
    K.emeasure_eq_measure[of s "{t\<in>S. P t}"]
  by (auto simp add: subset_eq K_def space_point_measure)

lemma emeasure_eq_sum:
  assumes s[simp]: "s \<in> S" and X[measurable]: "X \<in> sets S_seq"
  shows "emeasure (paths s) X = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S)))"
  by (simp add: prob_iterate measure_nonneg emeasure_eq_measure space_PiM PiE_def integral_K)

lemma prob_eq_sum:
  assumes s[simp]: "s \<in> S" and X[measurable]: "X \<in> sets S_seq"
  shows "prob s X = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S)))"
  by (simp add: prob_iterate measure_nonneg space_PiM integral_K PiE_def)

lemma positive_integral_eq_sum:
  assumes [simp]: "s \<in> S" and [measurable]: "f \<in> borel_measurable S_seq"
  shows "(\<integral>\<^isup>+x. f x \<partial>paths s) = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. f (nat_case s' x) \<partial>paths s'))"
  by (subst positive_integral_iterate)
     (simp_all add: space_PiM positive_integral_K positive_integral_positive)

lemma integral_eq_sum:
  assumes [simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "(\<integral>x. f x \<partial>paths s) = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>x. f (nat_case s' x) \<partial>paths s'))"
  by (subst integral_iterate) (simp_all add: space_PiM integral_K positive_integral_positive f)

lemma measure_space_S[simp]: "measure (paths s) (UNIV \<rightarrow> S) = 1"
  using prob_space by (simp add: space_PiM PiE_def)

lemma measure_space_S_seq[simp]: "measure (paths s) (space S_seq) = 1"
  using prob_space by simp

lemma space_Int_subset[simp]: "X \<inter> (UNIV \<rightarrow> S) \<subseteq> space S_seq"
  by (simp add: space_PiM PiE_def) 

lemma space_in_S_seq[measurable]: "UNIV \<rightarrow> S \<in> sets S_seq"
  using top[of S_seq] by (simp add: space_PiM PiE_def) 

lemma measurable_Collect_Pi[measurable (raw)]: 
  "Sigma_Algebra.pred S_seq P \<Longrightarrow> {\<omega>\<in>UNIV \<rightarrow> S. P \<omega>} \<in> sets S_seq"
  unfolding pred_def by (simp add: space_PiM PiE_def)

lemma AE_all_in_S: "AE \<omega> in paths s. \<forall>i. \<omega> i \<in> S"
  using AE_space[of "paths s"] by (auto simp: space_PiM)

lemma independent_cylinder:
  assumes s: "s \<in> S"
  assumes A: "\<And>n. A n \<subseteq> S"
  assumes p: "\<And>i a a'. i < n \<Longrightarrow> a \<in> nat_case {s} A i \<Longrightarrow> a' \<in> A i \<Longrightarrow> \<tau> a a' = p a' i"
  shows "\<P>(\<omega> in paths s. (\<forall>i<n. \<omega> i \<in> A i)) = (\<Prod>i<n. (\<Sum>a\<in>A i. p a i))"
proof -
  { fix i s' assume "i \<le> n" "s' \<in> nat_case {s} A i"
    then have "\<P>(\<omega> in paths s'. (\<forall>j\<in>{i..<n}. \<omega> (j - i) \<in> A j)) = (\<Prod>i\<in>{i..<n}. (\<Sum>a\<in>A i. p a i))"
    proof (induct arbitrary: s' rule: inc_induct)
      case base then show ?case by simp
    next
      case (step i)
      with s A
      have eq: "{i ..< n} = insert i {Suc i ..< n}" and s'[simp]: "s' \<in> S"
        by (auto split: nat.split_asm)
      have "\<P>(\<omega> in paths s'. (\<forall>j\<in>{i ..< n}. \<omega> (j - i) \<in> A j)) = 
          \<P>(\<omega> in paths s'. \<omega> 0 \<in> A i \<and> (\<forall>j\<in>{Suc i ..< n}. \<omega> (Suc (j - Suc i)) \<in> A j))"
        unfolding eq by (auto intro!: arg_cong2[where f=measure] simp: Suc_diff_Suc)
      also have "\<dots> = (\<Sum>a\<in>A i. p a i * \<P>(\<omega> in paths a. (\<forall>j\<in>{Suc i ..< n}. \<omega> (j - Suc i) \<in> A j)))"
        using A `i < n` p[of i s'] step.prems
        by (subst prob_eq_sum)
           (auto simp: space_PiM PiE_def
                 intro!: setsum_mono_zero_cong_right arg_cong2[where f="op *"] arg_cong2[where f=measure])
      also have "\<dots> = (\<Sum>a\<in>A i. p a i * (\<Prod>i\<in>{Suc i ..< n}. (\<Sum>a\<in>A i. p a i)))"
        by (intro setsum_cong[OF refl], subst step(2)) auto
      finally show "\<P>(\<omega> in paths s'. (\<forall>j\<in>{i ..< n}. \<omega> (j - i) \<in> A j)) = (\<Prod>i\<in>{i ..< n}. (\<Sum>a\<in>A i. p a i))"
        by (simp add: eq setsum_left_distrib)
    qed }
  from this[of 0 s] s show ?thesis by (simp add: Ball_def atLeast0LessThan)
qed

end

locale Rewarded_DTMC = Discrete_Time_Markov_Chain S \<tau> s0
    for S s0 and \<tau> :: "'s \<Rightarrow> 's \<Rightarrow> real" +
  fixes \<iota> :: "'s \<Rightarrow> 's \<Rightarrow> real" and \<rho> :: "'s \<Rightarrow> real"
  assumes \<iota>_nneg[simp, intro]: "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> 0 \<le> \<iota> s s'"
  assumes \<rho>_nneg[simp, intro]: "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> \<rho> s"
begin

definition "reward_until \<Phi> \<omega> =
  (if \<exists>i. \<omega> i \<in> \<Phi> then \<Sum>i<hitting_time \<Phi> \<omega>. \<rho> (\<omega> i) + \<iota> (\<omega> i) (\<omega> (Suc i)) else \<infinity>)"

lemma measurable_\<rho>[measurable]:
  "\<rho> \<in> borel_measurable (count_space S)"
proof -
  have "simple_function (count_space S) \<rho>"
    using finite_S unfolding simple_function_count_space by auto
  then show "\<rho> \<in> borel_measurable (count_space S) "
    by simp
qed

lemma measurable_\<iota>[measurable (raw)]: 
  assumes f[measurable]: "f \<in> measurable M (count_space S)"
  assumes g[measurable]: "g \<in> measurable M (count_space S)"
  shows "(\<lambda>\<omega>. \<iota> (f \<omega>) (g \<omega>)) \<in> borel_measurable M"
  unfolding measurable_def
proof safe
  fix A :: "real set" assume "A \<in> sets borel"
  with finite_S have "{\<omega>\<in>space M. \<exists>s\<in>S. \<exists>s'\<in>S. f \<omega> = s \<and> g \<omega> = s' \<and> \<iota> s s' \<in> A} \<in> sets M"
    by measurable
  also have "{\<omega>\<in>space M. \<exists>s\<in>S. \<exists>s'\<in>S. f \<omega> = s \<and> g \<omega> = s' \<and> \<iota> s s' \<in> A} = 
    (\<lambda>\<omega>. \<iota> (f \<omega>) (g \<omega>)) -` A \<inter> space M"
    using measurable_space[OF f] measurable_space[OF g] by auto
  finally show "(\<lambda>\<omega>. \<iota> (f \<omega>) (g \<omega>)) -` A \<inter> space M \<in> sets M" .
qed simp

lemma reward_until_measurable[measurable]: "reward_until \<Phi> \<in> borel_measurable S_seq"
  unfolding reward_until_def[abs_def] by measurable

lemma reward_until_nat_case_Suc:
  "s \<in> S \<Longrightarrow> s \<notin> \<Phi> \<Longrightarrow> nat_case s \<omega> \<in> until S \<Phi> \<Longrightarrow>
    reward_until \<Phi> (nat_case s \<omega>) = \<rho> s + \<iota> s (\<omega> 0) + reward_until \<Phi> \<omega>"
  by (auto simp add: reward_until_def hitting_time_nat_case_Suc lessThan_Suc_eq_insert_0 setsum_reindex zero_notin_Suc_image
           intro!: exI[of _ "hitting_time \<Phi> (nat_case s \<omega>)"])

lemma reward_until_nat_case_0:
  "s \<in> \<Phi> \<Longrightarrow> reward_until \<Phi> (nat_case s \<omega>) = 0"
  by (auto simp add: reward_until_def hitting_time_nat_case_0 intro!: exI[of _ 0])

lemma reward_until_positive:
  "\<omega> \<in> space S_seq \<Longrightarrow> 0 \<le> reward_until \<Phi> \<omega>"
  by (auto simp: reward_until_def space_PiM intro!: setsum_nonneg add_nonneg_nonneg)

lemma positive_integral_reward_until_ereal:
  assumes s[simp]: "s \<notin> \<Phi>" "s \<in> S" and until: "AE \<omega> in paths s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>paths s) =
   (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s' + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>paths s'))"
proof -
  have positive: "\<And>s. s \<in> S \<Longrightarrow> AE \<omega> in paths s. 0 \<le> reward_until \<Phi> (nat_case s \<omega>)"
    by (auto intro!: reward_until_positive simp: space_PiM PiE_iff split: nat.split)

  have "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>paths s) =
      (\<integral>\<^isup>+ \<omega>. \<rho> s + \<iota> s (\<omega> 0) + reward_until \<Phi> \<omega> \<partial>paths s)"
    using until by (intro positive_integral_cong_AE) (auto simp: reward_until_nat_case_Suc)
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s' + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>paths s'))"
    using emeasure_space_1
    by (subst positive_integral_eq_sum) (simp_all add: positive_integral_add positive)
  finally show ?thesis .
qed

lemma positive_integral_reward_until_finite:
  assumes s[simp]: "s \<in> S"
    and ae: "AE \<omega> in paths s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "\<bar>\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>paths s\<bar> \<noteq> \<infinity>"
    (is "\<bar>?R\<bar> \<noteq> \<infinity>")
proof (rule ereal_infinity_cases)
  def M \<equiv> "Max ((\<lambda>(s, s'). \<rho> s + \<iota> s s') ` (S\<times>S))"
  then have M: "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> \<rho> s + \<iota> s s' \<le> M" 
    by (auto intro!: Max_ge)
  from this[OF s0 s0] \<iota>_nneg[OF s0 s0] \<rho>_nneg[OF s0] have [arith]: "0 \<le> M"
    by auto
    
  have "?R \<le> (\<integral>\<^isup>+ \<omega>. M * hitting_time \<Phi> (nat_case s \<omega>) \<partial>paths s)"
    using ae
  proof (intro positive_integral_mono_AE, elim AE_mp, intro AE_I2 impI)
    fix \<omega> assume "nat_case s \<omega> \<in> until S \<Phi>" "\<omega> \<in> space (paths s)"
    from hitting_time_in[OF this(1)] `s \<in> S` this(2)
    have "reward_until \<Phi> (nat_case s \<omega>) \<le> (\<Sum>i<hitting_time \<Phi> (nat_case s \<omega>). M)"
      by (auto intro!: setsum_mono M exI[of _ "hitting_time \<Phi> (nat_case s \<omega>)"]
               simp: reward_until_def space_PiM Pi_iff split: nat.split
               simp del: setsum_constant)
    then show "reward_until \<Phi> (nat_case s \<omega>) \<le> M * hitting_time \<Phi> (nat_case s \<omega>)"
      by (simp add: real_eq_of_nat ac_simps)
  qed
  also have "\<dots> = M * (\<integral>\<^isup>+ \<omega>. hitting_time \<Phi> (nat_case s \<omega>) \<partial>paths s)"
    by (subst positive_integral_cmult[symmetric])
       (auto simp: comp_def real_eq_of_nat cong: measurable_cong_sets)
  also have "\<dots> < \<infinity>"
    using positive_integral_hitting_time_finite[OF s(1) _ ae]
    by (simp add: real_eq_of_nat)
  finally show "?R \<noteq> \<infinity>" by simp
next
  have "0 \<le> ?R"
    by (auto intro: positive_integral_positive)
  then show "?R \<noteq> -\<infinity>"
    by auto
qed

lemma positive_integral_reward_until_real:
  assumes s: "s \<notin> \<Phi>" "s \<in> S"
    and ae: "AE \<omega> in paths s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>paths s) =
   ereal (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s' + real (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>paths s')))"
    (is "?R s = _")
  unfolding positive_integral_reward_until_ereal[OF s ae]
proof (subst setsum_ereal[symmetric], intro setsum_cong refl)
  fix s' assume s': "s' \<in> S"
  { assume \<tau>: "\<tau> s s' \<noteq> 0"
    from ae s have "\<forall>s'\<in>E s. AE \<omega> in paths s'. nat_case s' \<omega> \<in> until S \<Phi>"
      by (simp add: AE_iterate[OF `s\<in>S`] AE_K_iff)
    from this[THEN bspec, of s']
    have "AE \<omega> in paths s'. nat_case s' \<omega> \<in> until S \<Phi>"
      using s \<tau> `s' \<in> S` by (simp add: E_iff)
    from positive_integral_reward_until_finite[OF `s' \<in> S` this]
    have "\<exists>r. ?R s' = ereal r"
      by auto }
  then show "\<tau> s s' * (\<rho> s + \<iota> s s' + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>paths s') =
        ereal (\<tau> s s' * (\<rho> s + \<iota> s s' + real (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>paths s')))"
    by (cases "\<tau> s s' = 0") (auto simp: zero_ereal_def[symmetric])
qed

end

end
