(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)
header {* Discrete Time Markov Chains with rewards *}
theory Rewarded_DTMC
  imports Discrete_Time_Markov_Chain
begin

lemma ereal_infinity_cases: "(a::ereal) \<noteq> \<infinity> \<Longrightarrow> a \<noteq> -\<infinity> \<Longrightarrow> \<bar>a\<bar> \<noteq> \<infinity>"
  by auto

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

lemma reward_until_measurable[measurable]: "reward_until \<Phi> \<in> borel_measurable p_space"
proof -
  have "(\<lambda>\<omega>. \<Sum>i<hitting_time \<Phi> \<omega>. \<rho> (\<omega> i) + \<iota> (\<omega> i) (\<omega> (Suc i))) \<in> borel_measurable p_space"
    unfolding hitting_time_def
    by (auto intro!: borel_measurable_setsum_dependent_index measurable_Least)
  then show ?thesis
    by (auto intro!: measurable_If sets_Collect simp: reward_until_def [abs_def])
qed

lemma reward_until_nat_case_Suc:
  "s \<in> S \<Longrightarrow> s \<notin> \<Phi> \<Longrightarrow> nat_case s \<omega> \<in> until S \<Phi> \<Longrightarrow> reward_until \<Phi> (nat_case s \<omega>) = \<rho> s + \<iota> s (\<omega> 0) + reward_until \<Phi> \<omega>"
  by (auto simp add: reward_until_def hitting_time_nat_case_Suc lessThan_Suc_eq_insert_0 setsum_reindex zero_notin_Suc_image
           intro!: exI[of _ "hitting_time \<Phi> (nat_case s \<omega>)"])

lemma reward_until_nat_case_0:
  "s \<in> \<Phi> \<Longrightarrow> reward_until \<Phi> (nat_case s \<omega>) = 0"
  by (auto simp add: reward_until_def hitting_time_nat_case_0 intro!: exI[of _ 0])

lemma reward_until_positive:
  "\<omega> \<in> UNIV \<rightarrow> S \<Longrightarrow> 0 \<le> reward_until \<Phi> \<omega>"
  by (auto simp: reward_until_def intro!: setsum_nonneg add_nonneg_nonneg)

lemma positive_integral_reward_until_ereal:
  assumes s: "s \<notin> \<Phi>" "s \<in> S" and ae: "AE \<omega> in path_space s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>path_space s) =
   (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s' + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s'))"
proof (subst positive_integral_eq_sum)
  show "s \<in> S" using assms by auto
  { fix s assume "s \<in> S"
    have "reward_until \<Phi> \<circ> nat_case s \<in> borel_measurable p_space"
      by (rule measurable_comp measurable_nat_case reward_until_measurable `s \<in> S`)+
    then have "(\<lambda>\<omega>. reward_until \<Phi> (nat_case s \<omega>)) \<in> borel_measurable p_space"
      by (simp add: comp_def) }
  note reward_next = this
  with s show "(\<lambda>\<omega>. reward_until \<Phi> (nat_case s \<omega>)) \<in> borel_measurable p_space"
    by simp

  { fix s' assume s': "s' \<in> S"
    { assume \<tau>: "\<tau> s s' \<noteq> 0"
      from ae have "AE \<omega> in path_space s. \<omega> \<in> nat_case s -` until S \<Phi>" by simp
      from AE_split[OF this _ `s \<in> S` s']
      have "AE \<omega> in path_space s'. \<omega> \<in> nat_case s' -` until S \<Phi>"
        using s \<tau> by simp
      with s have "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s (nat_case s' \<omega>)) \<partial>path_space s') =
        (\<integral>\<^isup>+ \<omega>. \<rho> s + \<iota> s s' + reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s')"
        by (intro positive_integral_cong_AE) (auto simp: reward_until_nat_case_Suc)
      also have "\<dots> = (\<integral>\<^isup>+ \<omega>. \<rho> s + \<iota> s s' \<partial>path_space s') + (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s')"
        using s s'
        by (intro positive_integral_add AE_I2 reward_until_positive add_nonneg_nonneg)
           (auto cong: measurable_cong_sets intro: reward_next)
      finally have "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s (nat_case s' \<omega>)) \<partial>path_space s') =
        \<rho> s + \<iota> s s' + (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s')"
        using s s' emeasure_space_1 by simp }
    then have "\<tau> s s' * (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s (nat_case s' \<omega>)) \<partial>path_space s') =
        \<tau> s s' * (\<rho> s + \<iota> s s' + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s')"
      by (cases "\<tau> s s' = 0") (auto simp: zero_ereal_def[symmetric]) }
  then show "(\<Sum>s'\<in>S. ereal (\<tau> s s') * \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s (nat_case s' \<omega>)) \<partial>path_space s') =
    (\<Sum>s'\<in>S. ereal (\<tau> s s') * (ereal (\<rho> s + \<iota> s s') + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s'))"
    by simp
qed

lemma positive_integral_reward_until_finite:
  assumes s[simp]: "s \<in> S" "\<Phi> \<subseteq> S"
    and ae: "AE \<omega> in path_space s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "\<bar>\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>path_space s\<bar> \<noteq> \<infinity>"
    (is "\<bar>?R\<bar> \<noteq> \<infinity>")
proof (rule ereal_infinity_cases)
  def M \<equiv> "Max ((\<lambda>(s, s'). \<rho> s + \<iota> s s') ` (S\<times>S))"
  then have M: "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> \<rho> s + \<iota> s s' \<le> M" 
    by (auto intro!: Max_ge)
  from this[OF s0 s0] \<iota>_nneg[OF s0 s0] \<rho>_nneg[OF s0] have [arith]: "0 \<le> M"
    by auto
    
  have "?R \<le> (\<integral>\<^isup>+ \<omega>. M * hitting_time \<Phi> (nat_case s \<omega>) \<partial>path_space s)"
    using ae
  proof (intro positive_integral_mono_AE, elim AE_mp, intro AE_I2 impI)
    fix \<omega> assume "nat_case s \<omega> \<in> until S \<Phi>" "\<omega> \<in> space (path_space s)"
    from hitting_time_in[OF this(1)] `s \<in> S` this(2)
    have "reward_until \<Phi> (nat_case s \<omega>) \<le> (\<Sum>i<hitting_time \<Phi> (nat_case s \<omega>). M)"
      by (auto intro!: setsum_mono M simp: reward_until_def
               simp del: setsum_constant)
    then show "reward_until \<Phi> (nat_case s \<omega>) \<le> M * hitting_time \<Phi> (nat_case s \<omega>)"
      by (simp add: real_eq_of_nat ac_simps)
  qed
  also have "\<dots> = M * (\<integral>\<^isup>+ \<omega>. hitting_time \<Phi> (nat_case s \<omega>) \<partial>path_space s)"
    by (subst positive_integral_cmult[symmetric])
       (auto simp: comp_def real_eq_of_nat cong: measurable_cong_sets)
  also have "\<dots> < \<infinity>"
    using positive_integral_hitting_time_finite[OF s(1,2) ae]
    by (simp add: real_eq_of_nat)
  finally show "?R \<noteq> \<infinity>" by simp
next
  have "0 \<le> ?R"
    by (auto intro: positive_integral_positive)
  then show "?R \<noteq> -\<infinity>"
    by auto
qed

lemma positive_integral_reward_until_real:
  assumes s: "s \<notin> \<Phi>" "s \<in> S" and \<Phi>: "\<Phi> \<subseteq> S"
    and ae: "AE \<omega> in path_space s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "(\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s \<omega>) \<partial>path_space s) =
   ereal (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s' + real (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s')))"
    (is "?R s = _")
  unfolding positive_integral_reward_until_ereal[OF s ae]
proof (subst setsum_ereal[symmetric], intro setsum_cong refl)
  fix s' assume s': "s' \<in> S"
  { assume \<tau>: "\<tau> s s' \<noteq> 0"
    from ae have "AE \<omega> in path_space s. \<omega> \<in> nat_case s -` until S \<Phi>" by simp
    from AE_split[OF this _ `s \<in> S` s']
    have "AE \<omega> in path_space s'. nat_case s' \<omega> \<in> until S \<Phi>"
      using s \<tau> by simp
    from positive_integral_reward_until_finite[OF `s' \<in> S` `\<Phi> \<subseteq> S` this]
    have "\<exists>r. ?R s' = ereal r"
      by auto }
  then show "\<tau> s s' * (\<rho> s + \<iota> s s' + \<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s') =
        ereal (\<tau> s s' * (\<rho> s + \<iota> s s' + real (\<integral>\<^isup>+ \<omega>. reward_until \<Phi> (nat_case s' \<omega>) \<partial>path_space s')))"
    by (cases "\<tau> s s' = 0") (auto simp: zero_ereal_def[symmetric])
qed

end

end