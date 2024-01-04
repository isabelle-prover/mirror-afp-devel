section \<open>Preliminary results\<close>

theory Concentration_Inequalities_Preliminary
  imports Lp.Lp
begin

text \<open>Version of Cauchy-Schwartz for the Lebesgue integral:\<close>
lemma cauchy_schwartz:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "integrable M (\<lambda>x. (f x) ^2)" "integrable M (\<lambda>x. (g x) ^2)"
  shows "integrable M (\<lambda>x. f x * g x)" (is "?A")
        "(\<integral>x. f x * g x \<partial>M) \<le> (\<integral>x. (f x)^2 \<partial>M) powr (1/2) * (\<integral>x. (g x)^ 2 \<partial>M) powr (1/2)"
        (is "?L \<le> ?R")
proof -
  show 0:"?A"
    using assms by (intro Holder_inequality(1)[where p="2" and q="2"]) auto

  have "?L \<le> (\<integral>x. \<bar>f x * g x\<bar> \<partial>M)"
    using 0 by (intro integral_mono) auto
  also have "... \<le> (\<integral>x. \<bar>f x\<bar> powr 2 \<partial>M) powr (1/2) * (\<integral>x. \<bar>g x\<bar> powr 2 \<partial>M) powr (1/2)"
    using assms by (intro Holder_inequality(2)) auto
  also have "... = ?R" by simp
  finally show "?L \<le> ?R" by simp
qed

text \<open>Generalization of @{thm [source] prob_space.indep_vars_iff_distr_eq_PiM'}:\<close>

lemma (in prob_space) indep_vars_iff_distr_eq_PiM'':
  fixes I :: "'i set" and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X i)"
  shows "indep_vars M' X I \<longleftrightarrow>
           distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
proof (cases "I = {}")
  case True
  have 0: " indicator A (\<lambda>_. undefined) = emeasure (count_space {\<lambda>_. undefined}) A" (is "?L = ?R")
    if "A \<subseteq> {\<lambda>_. undefined}" for A :: "('i \<Rightarrow> 'b) set"
  proof -
    have 1:"A \<noteq> {} \<Longrightarrow> A = {\<lambda>_. undefined}"
      using that by auto

    have "?R = of_nat (card A)"
      using finite_subset that by (intro emeasure_count_space_finite that) auto
    also have "... = ?L"
      using 1 by (cases "A = {}") auto
    finally show ?thesis by simp
  qed

  have "distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) =
    distr M (count_space {\<lambda>_. undefined}) (\<lambda>_. (\<lambda>_. undefined))"
    unfolding True PiM_empty by (intro distr_cong) (auto simp:restrict_def)
  also have "... = return (count_space {\<lambda>_. undefined}) (\<lambda>_. undefined)"
    by (intro distr_const) auto
  also have "... = count_space ({\<lambda>_. undefined} :: ('i \<Rightarrow> 'b) set) "
    by (intro measure_eqI) (auto simp:0)
  also have "... = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
    unfolding True PiM_empty by simp
  finally have "distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x)=(\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i)) \<longleftrightarrow> True"
    by simp
  also have "... \<longleftrightarrow> indep_vars M' X I"
    unfolding indep_vars_def by (auto simp add: space_PiM indep_sets_def) (auto simp add:True)
  finally show ?thesis by simp
next
  case False
  thus ?thesis
    by (intro indep_vars_iff_distr_eq_PiM' assms) auto
qed

lemma proj_indep:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  shows "prob_space.indep_vars (PiM I M) M (\<lambda>i \<omega>. \<omega> i) I"
proof -
  interpret prob_space "(PiM I M)"
    by (intro prob_space_PiM assms)

  have "distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. restrict x I) = PiM I M"
    by (intro distr_PiM_reindex assms) auto
  also have "... =  Pi\<^sub>M I (\<lambda>i. distr (Pi\<^sub>M I M) (M i) (\<lambda>\<omega>. \<omega> i))"
    by (intro PiM_cong refl distr_PiM_component[symmetric] assms)
  finally have
    "distr (Pi\<^sub>M I M) (Pi\<^sub>M I M) (\<lambda>x. restrict x I) = Pi\<^sub>M I (\<lambda>i. distr (Pi\<^sub>M I M) (M i) (\<lambda>\<omega>. \<omega> i))"
    by simp
  thus "indep_vars M (\<lambda>i \<omega>. \<omega> i) I"
    by (intro iffD2[OF indep_vars_iff_distr_eq_PiM'']) simp_all
qed

lemma forall_Pi_to_PiE:
  assumes "\<And>x. P x = P (restrict x I)"
  shows "(\<forall>x \<in> Pi I A. P x) = (\<forall>x \<in> PiE I A. P x)"
  using assms by (simp add:PiE_def Pi_def set_eq_iff, force)

lemma PiE_reindex:
  assumes "inj_on f I"
  shows "PiE I (A \<circ> f) = (\<lambda>a. restrict (a \<circ> f) I) ` PiE (f ` I) A" (is "?lhs = ?g ` ?rhs")
proof -
  have "?lhs \<subseteq> ?g` ?rhs"
  proof (rule subsetI)
    fix x
    assume a:"x \<in> Pi\<^sub>E I (A \<circ> f)"
    define y where y_def: "y = (\<lambda>k. if k \<in> f ` I then x (the_inv_into I f k) else undefined)"
    have b:"y \<in> PiE (f ` I) A"
      using a assms the_inv_into_f_eq[OF assms]
      by (simp add: y_def PiE_iff extensional_def)
    have c: "x = (\<lambda>a. restrict (a \<circ> f) I) y"
      using a assms the_inv_into_f_eq extensional_arb
      by (intro ext, simp add:y_def PiE_iff, fastforce)
    show "x \<in> ?g ` ?rhs" using b c by blast
  qed
  moreover have "?g ` ?rhs \<subseteq> ?lhs"
    by (rule image_subsetI, simp add:Pi_def PiE_def)
  ultimately show ?thesis by blast
qed

context prob_space
begin

lemma indep_sets_reindex:
  assumes "inj_on f I"
  shows "indep_sets A (f ` I) = indep_sets (\<lambda>i. A (f i)) I"
proof -
  have a: "\<And>J g. J \<subseteq> I \<Longrightarrow> (\<Prod>j \<in> f ` J. g j) = (\<Prod>j \<in> J. g (f j))"
    by (metis assms prod.reindex_cong subset_inj_on)

  have b:"J \<subseteq> I \<Longrightarrow> (\<Pi>\<^sub>E i \<in> J. A (f i)) = (\<lambda>a. restrict (a \<circ> f) J) ` PiE (f ` J) A" for J
    using assms inj_on_subset
    by (subst PiE_reindex[symmetric]) auto

  have c:"\<And>J. J \<subseteq> I \<Longrightarrow> finite (f ` J) = finite J"
    by (meson assms finite_image_iff inj_on_subset)

  show ?thesis
    by (simp add:indep_sets_def all_subset_image a c) (simp_all add:forall_Pi_to_PiE b)
qed

lemma indep_vars_reindex:
  assumes "inj_on f I"
  assumes "indep_vars M' X' (f ` I)"
  shows "indep_vars (M' \<circ> f) (\<lambda>k \<omega>. X' (f k) \<omega>) I"
  using assms by (simp add:indep_vars_def2 indep_sets_reindex)

lemma indep_vars_cong_AE:
  assumes "AE x in M. (\<forall>i \<in> I. X' i x = Y' i x)"
  assumes "indep_vars M' X' I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (Y' i)"
  shows "indep_vars M' Y' I"
proof -
  have a: "AE x in M. (\<lambda>i\<in>I. Y' i x) = (\<lambda>i\<in>I. X' i x)"
    by (rule AE_mp[OF assms(1)], rule AE_I2, simp cong:restrict_cong)
  have b: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X' i)"
    using assms(2) by (simp add:indep_vars_def2)
  have c: "\<And>x. x \<in> I \<Longrightarrow> AE xa in M. X' x xa = Y' x xa"
    by (rule AE_mp[OF assms(1)], rule AE_I2, simp)

  have "distr M (Pi\<^sub>M I M') (\<lambda>x. \<lambda>i\<in>I. Y' i x) = distr M (Pi\<^sub>M I M') (\<lambda>x. \<lambda>i\<in>I. X' i x)"
    by (intro distr_cong_AE measurable_restrict a b assms(3)) auto
  also have "... =  Pi\<^sub>M I (\<lambda>i. distr M (M' i) (X' i))"
    using assms b by (subst indep_vars_iff_distr_eq_PiM''[symmetric]) auto
  also have "... =  Pi\<^sub>M I (\<lambda>i. distr M (M' i) (Y' i))"
    by (intro PiM_cong distr_cong_AE c assms(3) b) auto
  finally have "distr M (Pi\<^sub>M I M') (\<lambda>x. \<lambda>i\<in>I. Y' i x) = Pi\<^sub>M I (\<lambda>i. distr M (M' i) (Y' i))"
    by simp

  thus ?thesis
    using assms(3)
    by (subst indep_vars_iff_distr_eq_PiM'') auto
qed

end

text \<open>Integrability of bounded functions on finite measure spaces:\<close>

lemma bounded_const: "bounded ((\<lambda>x. (c::real)) ` T)"
  by (intro boundedI[where B="norm c"]) auto

lemma bounded_exp:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bounded ((\<lambda>x. f x) ` T)"
  shows "bounded ((\<lambda>x. exp (f x)) ` T)"
proof -
  obtain m where "norm (f x) \<le> m" if "x \<in> T" for x
    using assms unfolding bounded_iff by auto

  thus ?thesis
    by (intro boundedI[where B="exp m"]) fastforce
qed

lemma bounded_mult_comp:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bounded (f ` T)" "bounded (g ` T)"
  shows "bounded ((\<lambda>x. (f x) * (g x)) ` T)"
proof -
  obtain m1 where "norm (f x) \<le> m1" "m1 \<ge>0" if "x \<in> T" for x
    using assms unfolding bounded_iff by fastforce
  moreover obtain m2 where "norm (g x) \<le> m2" "m2 \<ge>0" if "x \<in> T" for x
    using assms unfolding bounded_iff by fastforce

  ultimately show ?thesis
    by (intro boundedI[where B="m1 * m2"]) (auto intro!: mult_mono simp:abs_mult)
qed

lemma bounded_sum:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> bounded (f i ` T)"
  shows "bounded ((\<lambda>x. (\<Sum>i \<in> I. f i x)) ` T)"
  using assms by (induction I) (auto intro:bounded_plus_comp bounded_const)

lemma (in finite_measure) bounded_int:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes "bounded ((\<lambda> x. f (fst x) (snd x)) ` (T \<times> space M))"
  shows "bounded ((\<lambda>x. (\<integral>\<omega>. (f x \<omega>) \<partial>M)) ` T)"
proof -
  obtain m where "\<And>x y. x \<in> T \<Longrightarrow> y \<in> space M \<Longrightarrow> norm (f x y) \<le> m"
    using assms unfolding bounded_iff by auto
  hence m:"\<And>x y. x \<in> T \<Longrightarrow> y \<in> space M \<Longrightarrow> norm (f x y) \<le> max m 0"
    by fastforce

  have "norm (\<integral>\<omega>. (f x \<omega>) \<partial>M) \<le> max m 0 * measure M (space M)" (is "?L \<le> ?R") if "x \<in> T" for x
  proof -
    have "?L \<le> (\<integral>\<omega>. norm (f x \<omega>) \<partial>M)" by simp
    also have "... \<le> (\<integral>\<omega>. max m 0 \<partial>M)"
      using that m by (intro integral_mono') auto
    also have "... = ?R"
      by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    by (intro boundedI[where B="max m 0 * measure M (space M)"]) auto
qed

lemmas bounded_intros =
  bounded_minus_comp bounded_plus_comp bounded_mult_comp bounded_sum finite_measure.bounded_int
  bounded_const bounded_exp

lemma (in prob_space) integrable_bounded:
  fixes f :: "_ \<Rightarrow> ('b :: {banach,second_countable_topology})"
  assumes "bounded (f ` space M)"
  assumes "f \<in> M \<rightarrow>\<^sub>M borel"
  shows "integrable M f"
proof -
  obtain m where "norm (f x) \<le> m" if "x \<in> space M" for x
    using assms(1) unfolding bounded_iff by auto
  thus ?thesis
    by (intro integrable_const_bound[where B="m"] AE_I2 assms(2))
qed

end