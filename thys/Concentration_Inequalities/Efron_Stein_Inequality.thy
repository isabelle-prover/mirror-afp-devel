section \<open>Efron-Stein Inequality\<close>

text \<open>In this section we verify the Efron-Stein inequality. The verified theorem is stated as
Efron-Stein inequality for non-symmetric functions by Steele~\cite{steele1986}. However most
textbook refer to this version as ``the Efron-Stein inequality''. The original result that was shown
by Efron and Stein is a tail bound for the variance of a symmetric functions of i.i.d.
random variables~\cite{efron1981}.\<close>

theory Efron_Stein_Inequality
  imports Concentration_Inequalities_Preliminary
begin

theorem efron_stein_inequality_distr:
  fixes f :: "_ \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "integrable (PiM I M) (\<lambda>x. f x^2)" and f_meas: "f \<in> borel_measurable (PiM I M)"
  shows "prob_space.variance (PiM I M) f \<le>
    (\<Sum>i\<in>I. (\<integral>x. (f (\<lambda>j. x (j,False)) - f (\<lambda>j. x (j, j=i)))^2 \<partial>PiM (I\<times>UNIV) (M \<circ> fst))) / 2"
    (is "?L \<le> ?R")
proof -
  let ?M = "PiM (I\<times>(UNIV::bool set)) (M \<circ> fst)"

  have prob: "prob_space (PiM I M)"
    using assms(2) by (intro prob_space_PiM) auto

  interpret prob_space "?M"
    using assms(2) by (intro prob_space_PiM) auto

  define n where "n = card I"

  obtain q :: "_ \<Rightarrow> nat" where q:"bij_betw q I {..<n}"
    unfolding n_def using ex_bij_betw_finite_nat[OF assms(1)] atLeast0LessThan by auto

  let ?\<phi> = "(\<lambda>n x. f (\<lambda>j. x (j, q j < n)))"
  let ?\<tau> = "(\<lambda>n x. f (\<lambda>j. x (j, q j = n)))"
  let ?\<sigma> = "(\<lambda>x. f (\<lambda>j. x (j, False)))"
  let ?\<chi> = "(\<lambda>x. f (\<lambda>j. x (j, True)))"

  have meas_1: "(\<lambda>\<omega>. f (g \<omega>)) \<in> borel_measurable ?M"
    if "g \<in> Pi\<^sub>M (I \<times> UNIV) (M \<circ> fst) \<rightarrow>\<^sub>M Pi\<^sub>M I M" for g
    using that by (intro measurable_compose[OF _ f_meas])

  have meas_2: "(\<lambda>x j. x (j, h j)) \<in> ?M \<rightarrow>\<^sub>M Pi\<^sub>M I M" for h
  proof -
    have "?thesis \<longleftrightarrow> (\<lambda>x. (\<lambda>j \<in> I. x (j, h j))) \<in> ?M \<rightarrow>\<^sub>M Pi\<^sub>M I M"
      by (intro measurable_cong) (auto simp:space_PiM PiE_def extensional_def)
    also have "... \<longleftrightarrow> True"
      unfolding eq_True
      by (intro measurable_restrict measurable_PiM_component_rev) auto
    finally show ?thesis by simp
  qed

  have int_1: "integrable ?M (\<lambda>x. (g x - h x)^2)"
    if "integrable ?M (\<lambda>x. (g x)^2)"  "integrable ?M (\<lambda>x. (h x)^2)"
    and "g \<in> borel_measurable ?M" "h \<in> borel_measurable ?M"
    for g h :: "_ \<Rightarrow> real"
  proof -
    have "integrable ?M (\<lambda>x. (g x)^2 + (h x)^2 - 2 * (g x * h x))"
      using that by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff
          integrable_mult_right cauchy_schwartz(1))
    thus ?thesis by (simp add:algebra_simps power2_eq_square)
  qed

  note meas_rules = borel_measurable_add borel_measurable_times borel_measurable_diff
    borel_measurable_power meas_1 meas_2

  have f_int: "integrable (Pi\<^sub>M I M) f"
    by (intro finite_measure.square_integrable_imp_integrable[OF _ f_meas assms(3)]
        prob_space.finite_measure prob)
  moreover have "integrable (Pi\<^sub>M I M) (\<lambda>x. f (restrict x I)) = integrable (Pi\<^sub>M I M) f"
    by (intro  Bochner_Integration.integrable_cong) (auto simp:space_PiM)
  ultimately have f_int_2: "integrable (Pi\<^sub>M I M) (\<lambda>x. f (restrict x I))" by simp

  have cong: "(\<integral>x. g (\<lambda>j\<in>I. x (j, h j)) \<partial>?M) = (\<integral>x. g (\<lambda>j. x (j, h j)) \<partial>?M)" (is "?L1 = ?R1")
    for g :: "_ \<Rightarrow> real" and h
    by (intro Bochner_Integration.integral_cong arg_cong[where f="g"] refl)
       (auto simp add:space_PiM PiE_def extensional_def restrict_def)

  have lift: "(\<integral>x. g x \<partial>PiM I M) = (\<integral>x. g (\<lambda>j. x (j, h j)) \<partial>?M)" (is "?L1 = ?R1")
    if "g \<in> borel_measurable (Pi\<^sub>M I M)"
    for g :: "_ \<Rightarrow> real" and h
  proof -
    let ?J = "(\<lambda>i. (i, h i)) ` I"
    have "?R1 = (\<integral>x. g (\<lambda>j \<in> I. x (j, h j)) \<partial>?M)"
      by (intro cong[symmetric])
    also have "... = (\<integral>x. g x \<partial>distr ?M (PiM I (\<lambda>i. (M\<circ>fst) (i, h i))) (\<lambda>x. (\<lambda>j \<in> I. x (j, h j))))"
      using that
      by (intro integral_distr[symmetric] measurable_restrict measurable_component_singleton) auto
    also have "... = (\<integral>x. g x \<partial>PiM I (\<lambda>i. (M \<circ> fst) (i, h i)))"
      using assms(2)
      by (intro arg_cong2[where f="integral\<^sup>L"] refl distr_PiM_reindex inj_onI) auto
    also have "... = ?L1"
      by auto
    finally show ?thesis
      by simp
  qed

  have lift_int: "integrable ?M (\<lambda>x. g (\<lambda>j. x (j, h j)))" if "integrable (Pi\<^sub>M I M) g"
    for g :: "_ \<Rightarrow> real" and h
  proof -
    have 0:"integrable (distr ?M (PiM I (\<lambda>i. (M\<circ>fst) (i, h i))) (\<lambda>x. (\<lambda>j \<in> I. x (j, h j)))) g"
      using that assms(2) by (subst distr_PiM_reindex) (auto intro:inj_onI)
    have "integrable ?M (\<lambda>x. g (\<lambda>j\<in>I. x (j, h j)))"
      by (intro integrable_distr[OF _ 0] measurable_restrict measurable_component_singleton) auto
    moreover have "integrable ?M (\<lambda>x. g (\<lambda>j\<in>I. x (j, h j))) \<longleftrightarrow> ?thesis"
      by (intro Bochner_Integration.integrable_cong refl arg_cong[where f="g"] ext)
       (auto simp:PiE_def space_PiM extensional_def)
    ultimately show ?thesis
      by simp
  qed

  note int_rules = cauchy_schwartz(1) int_1 lift_int assms(3) f_int f_int_2

  have "(\<integral>x. g x \<partial>?M) = (\<integral>x. g (\<lambda>(j,v). x (j, v \<noteq> h j)) \<partial>?M)" (is "?L1 = ?R1")
    if "g \<in> borel_measurable ?M" for g :: "_ \<Rightarrow> real" and h
  proof -
    have "?L1 = (\<integral>x. g x \<partial>distr ?M (PiM (I\<times>UNIV) (\<lambda>i. (M \<circ> fst) (fst i, snd i \<noteq> h (fst i))))
      (\<lambda>x.(\<lambda>i \<in> I\<times>UNIV. x (fst i, snd i \<noteq> h (fst i))) ))"
      by (subst distr_PiM_reindex) (auto intro:inj_onI assms(2) simp:comp_def)
    also have "... = (\<integral>x. g (\<lambda>i \<in> I\<times>UNIV. x (fst i, snd i \<noteq> h (fst i))) \<partial>?M)"
      using that by (intro integral_distr measurable_restrict measurable_component_singleton)
        (auto simp:comp_def)
    also have "... = ?R1"
      by (intro Bochner_Integration.integral_cong refl arg_cong[where f="g"] ext)
       (auto simp add:space_PiM PiE_def extensional_def restrict_def)
    finally show ?thesis
      by simp
  qed

  hence switch: "(\<integral>x. g x \<partial>?M) = (\<integral>x. h x \<partial>?M)"
    if "\<And>x. h x = g (\<lambda>(j,v). x (j, v \<noteq> u j))" "g \<in> borel_measurable ?M"
    for g h :: "_ \<Rightarrow> real" and u
    using that by simp

  have 1: "(\<integral>x. (?\<sigma> x) * (?\<phi> i x - ?\<phi> (i+1) x) \<partial>?M) \<le> (\<integral>x. (?\<sigma> x - ?\<tau> i x)^2 \<partial>?M) / 2"
    (is "?L1 \<le> ?R1")
    if "i < n" for i
  proof -
    have "?L1 = (\<integral>x. (?\<tau> i x) * (?\<phi> (i+1) x - ?\<phi> i x) \<partial>?M)"
      by (intro switch[of _ _ "(\<lambda>j. q j = i)"] arg_cong2[where f="(*)"]
            arg_cong2[where f="(-)"] arg_cong[where f="f"] ext meas_rules) (auto intro:arg_cong)
    hence "?L1 = (?L1 + (\<integral>x. (?\<tau> i x) * (?\<phi> (i+1) x - ?\<phi> i x) \<partial>?M)) / 2"
      by simp
    also have "... = (\<integral>x. (?\<sigma> x) * (?\<phi> i x - ?\<phi>(i+1) x) + (?\<tau> i x) * (?\<phi>(i+1) x - ?\<phi> i x) \<partial>?M)/2"
      by (intro Bochner_Integration.integral_add[symmetric] arg_cong2[where f="(/)"] refl
          int_rules meas_rules)
    also have "... = (\<integral>x. (?\<sigma> x - ?\<tau> i x) * (?\<phi> i x - ?\<phi>(i+1) x) \<partial>?M)/2"
      by (intro arg_cong2[where f="(/)"] Bochner_Integration.integral_cong)
        (auto simp:algebra_simps)
    also have "...\<le>((\<integral>x. (?\<sigma> x-?\<tau> i x)^2 \<partial>?M)powr(1/2)*(\<integral>x.(?\<phi> i x-?\<phi>(i+1)x)^2 \<partial>?M) powr (1/2))/2"
      by (intro divide_right_mono cauchy_schwartz meas_rules int_rules) auto
    also have "...=((\<integral>x. (?\<sigma> x-?\<tau> i x)^2 \<partial>?M)powr(1/2)*(\<integral>x.(?\<sigma> x-?\<tau> i x)^2 \<partial>?M) powr (1/2))/2"
      by (intro arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] arg_cong2[where f="(powr)"] refl
         switch[of _ _ "(\<lambda>j. q j < i)"] arg_cong2[where f="power"] arg_cong2[where f="(-)"]
         arg_cong[where f="f"] ext meas_rules) (auto intro:arg_cong)
    also have "... = (\<integral>x. (?\<sigma> x-?\<tau> i x)^2 \<partial>?M)/2"
      by (simp add:powr_add[symmetric])
    finally show ?thesis by simp
  qed

  have "indep_vars (M \<circ> fst) (\<lambda>i \<omega>. \<omega> i) (I \<times> UNIV)"
    using assms(2) by (intro proj_indep) auto
  hence 2:"indep_var (Pi\<^sub>M (I\<times>{False}) (M\<circ>fst)) (\<lambda>x. \<lambda>j\<in>I\<times>{False}. x j)
    (Pi\<^sub>M (I\<times>{True}) (M\<circ>fst)) (\<lambda>x. \<lambda>j\<in>I\<times>{True}. x j)"
    by (intro indep_var_restrict[where I="I \<times> UNIV"]) auto
  have "indep_var
    (Pi\<^sub>M I M) ((\<lambda>x. (\<lambda>i \<in> I. x (i, False))) \<circ> (\<lambda>x. (\<lambda>j \<in> I\<times>{False}. x j)))
    (Pi\<^sub>M I M) ((\<lambda>x. (\<lambda>i \<in> I. x (i, True))) \<circ> (\<lambda>x. (\<lambda>j \<in> I\<times>{True}. x j)))"
    by (intro indep_var_compose[OF 2] measurable_restrict measurable_PiM_component_rev) auto
  hence "indep_var (Pi\<^sub>M I M) (\<lambda>x. (\<lambda>j\<in>I. x (j, False))) (Pi\<^sub>M I M) (\<lambda>x. (\<lambda>j\<in>I. x (j, True)))"
    unfolding comp_def by (simp add:restrict_def cong:if_cong)

  hence "indep_var borel (f \<circ> (\<lambda>x. (\<lambda>j\<in>I. x (j, False)))) borel (f \<circ> (\<lambda>x. (\<lambda>j \<in> I. x (j, True))))"
    by (intro indep_var_compose[OF _ assms(4,4)]) auto
  hence indep:"indep_var borel (\<lambda>x. f (\<lambda>j\<in>I. x (j, False))) borel (\<lambda>x. f (\<lambda>j\<in>I. x (j, True)))"
    by (simp add:comp_def)

  have 3: "\<omega> (j, q j = q i) = \<omega> (j, j = i)" if
    "\<omega> \<in> PiE (I \<times> UNIV) (\<lambda>i. space (M (fst i)))" "i \<in> I" for i j \<omega>
  proof (cases "j \<in> I")
    case True
    hence "(q j = q i) = (j = i)"
      using that inj_onD[OF bij_betw_imp_inj_on[OF q]] by blast
    thus ?thesis by simp
  next
    case False
    hence "\<omega> (j, a) = undefined" for a
      using that unfolding PiE_def extensional_def by simp
    thus ?thesis by simp
  qed

  have "?L = (\<integral>x. (f x)^2 \<partial>PiM I M) - (\<integral>x. (f x) \<partial>PiM I M)^2"
    by (intro prob_space.variance_eq f_int assms(3) prob)
  also have "... = (\<integral>x. (f x)^2 \<partial>PiM I M) - (\<integral>x. f x \<partial>PiM I M) * (\<integral>x. f x \<partial>PiM I M)"
    by (simp add:power2_eq_square)
  also have "... = (\<integral>x. (?\<sigma> x)^2 \<partial>?M) - (\<integral>x. ?\<sigma> x \<partial>?M) * (\<integral>x. ?\<chi> x \<partial>?M)"
    by (intro arg_cong2[where f="(-)"] lift  arg_cong2[where f="(*)"] meas_rules f_meas)
  also have "... = (\<integral>x. (?\<sigma> x)^2 \<partial>?M)-(\<integral>x. f (\<lambda>j\<in>I. x (j,False)) \<partial>?M)*(\<integral>x. f(\<lambda>j\<in>I. x(j,True)) \<partial>?M)"
    by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(*)"] cong[symmetric] refl)
  also have "... = (\<integral>x. (?\<sigma> x)^2 \<partial>?M) - (\<integral>x. f (\<lambda>j\<in>I. x (j,False))* f(\<lambda>j\<in>I. x(j,True))  \<partial>?M)"
    by (intro arg_cong2[where f="(-)"] indep_var_lebesgue_integral[symmetric] refl int_rules indep)
  also have "... = (\<integral>x. (?\<sigma> x) * (?\<phi> 0 x) \<partial>?M) - (\<integral>x. (?\<sigma> x) * (?\<phi> n x)  \<partial>?M)"
    using bij_betw_apply[OF q] by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(*)"] ext
        arg_cong[where f="f"] Bochner_Integration.integral_cong)
     (auto simp:space_PiM power2_eq_square PiE_def extensional_def)
  also have "... = (\<Sum>i < n. (\<integral>x. (?\<sigma> x) *  (?\<phi> i x)  \<partial>?M) -  (\<integral>x. (?\<sigma> x) *  (?\<phi> (Suc i) x) \<partial>?M))"
    unfolding power2_eq_square by (intro sum_lessThan_telescope'[symmetric])
  also have "... = (\<Sum>i < n. (\<integral>x. (?\<sigma> x) *  (?\<phi> i x) - (?\<sigma> x) *  (?\<phi> (Suc i) x) \<partial>?M))"
    by (intro sum.cong Bochner_Integration.integral_diff[symmetric] int_rules meas_rules) auto
  also have "... = (\<Sum>i < n. (\<integral>x. (?\<sigma> x) * (?\<phi> i x - ?\<phi> (i+1) x) \<partial>?M))"
    by (simp_all add:power2_eq_square algebra_simps)
  also have "... \<le> (\<Sum>i< n. ((\<integral>x. (?\<sigma> x - ?\<tau> i x)^2 \<partial>?M)) / 2)"
    by (intro sum_mono 1) auto
  also have "... = (\<Sum>i \<in> I. ((\<integral>x. (f (\<lambda>j. x (j,False)) - f (\<lambda>j. x (j,q j=q i)))^2 \<partial>?M))/ 2)"
    by (intro sum.reindex_bij_betw[OF q, symmetric])
  also have "... = (\<Sum>i \<in> I. ((\<integral>x. (f (\<lambda>j. x (j,False)) -  f (\<lambda>j. x (j,q j=q i)))^2 \<partial>?M)))/2"
    unfolding sum_divide_distrib[symmetric] by simp
  also have "... = ?R"
    using inj_onD[OF bij_betw_imp_inj_on[OF q]]
    by (intro arg_cong2[where f="(/)"] arg_cong2[where f="(-)"]  arg_cong2[where f="power"]
          arg_cong[where f="f"] Bochner_Integration.integral_cong sum.cong refl ext 3)
     (auto  simp add:space_PiM )
  finally show ?thesis
    by simp
qed

theorem (in prob_space) efron_stein_inequality_classic:
  fixes f :: "_ \<Rightarrow> real"
  assumes "finite I"
  assumes "indep_vars (M' \<circ> fst) X (I \<times> (UNIV :: bool set))"
  assumes "f \<in> borel_measurable (PiM I M')"
  assumes "integrable M (\<lambda>\<omega>. f (\<lambda>i\<in>I. X (i,False) \<omega>)^2)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> distr M (M' i) (X (i, True)) = distr M (M' i) (X (i, False))"
  shows "variance (\<lambda>\<omega>. f (\<lambda>i\<in>I. X (i,False) \<omega>)) \<le>
    (\<Sum>j \<in> I. expectation (\<lambda>\<omega>. (f (\<lambda>i\<in>I. X (i,False) \<omega>) - f (\<lambda>i\<in>I. X (i, i=j) \<omega>))^2))/2"
    (is "?L \<le> ?R")
proof -
  let ?D = "distr M (PiM I M') (\<lambda>\<omega>. \<lambda>i\<in>I. X (i, False) \<omega>)"

  let ?M = "PiM I (\<lambda>i. distr M (M' i) (X (i,False)))"
  let ?N = "PiM (I \<times> (UNIV::bool set)) ((\<lambda>i. distr M (M' i) (X (i,False))) \<circ> fst)"

  have rv: "random_variable (M' i) (X (i, j))" if "i \<in> I" for i j
    using assms(2) that unfolding indep_vars_def by auto

  have proj_meas: "(\<lambda>x j. x (j, h j)) \<in> Pi\<^sub>M (I \<times> UNIV) (M' \<circ> fst) \<rightarrow>\<^sub>M Pi\<^sub>M I M'"
    for h :: " _ \<Rightarrow> bool"
  proof -
    have "?thesis \<longleftrightarrow> (\<lambda>x. (\<lambda>j \<in> I. x (j, h j))) \<in> Pi\<^sub>M (I \<times> UNIV) (M' \<circ> fst) \<rightarrow>\<^sub>M Pi\<^sub>M I M'"
      by (intro measurable_cong) (auto simp:space_PiM PiE_def extensional_def)
    also have "... \<longleftrightarrow> True"
      unfolding eq_True
      by (intro measurable_restrict measurable_PiM_component_rev) auto
    finally show ?thesis by simp
  qed

  note meas_rules = borel_measurable_add borel_measurable_times borel_measurable_diff proj_meas
    borel_measurable_power assms(3) measurable_restrict measurable_compose[OF _ assms(3)]

  have "indep_vars ((M' \<circ> fst) \<circ> (\<lambda>i. (i, False))) (\<lambda>i. X (i, False)) I"
    by (intro indep_vars_reindex indep_vars_subset[OF assms(2)] inj_onI) auto
  hence "indep_vars M' (\<lambda>i. X (i, False)) I" by (simp add: comp_def)
  hence 0:"?D = PiM I (\<lambda>i. distr M (M' i) (X (i,False)))"
    by (intro iffD1[OF indep_vars_iff_distr_eq_PiM''] rv)

  have "distr M (M' (fst x)) (X (fst x, False)) = distr M (M' (fst x)) (X x)"
    if "x \<in> I \<times> UNIV" for x
    using that assms(5) by (cases x, cases "snd x") auto

  hence 1: "?N = PiM (I \<times> UNIV) (\<lambda>i. distr M ((M' \<circ> fst) i) (X i))"
    using assms(3) by (intro PiM_cong refl) (simp add:comp_def)
  also have "... = distr M (PiM (I \<times> UNIV) (M' \<circ> fst)) (\<lambda>x. \<lambda>i\<in>I \<times> UNIV. X i x)"
    using rv by (intro iffD1[OF indep_vars_iff_distr_eq_PiM'', symmetric] assms(2)) auto
  finally have 2:"?N = distr M (PiM (I \<times> UNIV) (M' \<circ> fst)) (\<lambda>x. \<lambda>i\<in>I \<times> UNIV. X i x)"
    by simp

  have 3: "integrable (Pi\<^sub>M I (\<lambda>i. distr M (M' i) (X (i, False)))) (\<lambda>x. (f x)\<^sup>2)"
    unfolding 0[symmetric] by (intro iffD2[OF integrable_distr_eq] meas_rules assms rv)

  have "?L = (\<integral>x. (f x - expectation (\<lambda>\<omega>. f (\<lambda>i\<in>I. X (i,False) \<omega>)))^2 \<partial>?D)"
    using rv by (intro integral_distr[symmetric] meas_rules measurable_restrict) auto
  also have "... = prob_space.variance ?D f"
    by (intro arg_cong[where f="integral\<^sup>L ?D"] arg_cong2[where f="(-)"] arg_cong2[where f="power"]
        refl ext integral_distr[symmetric] measurable_restrict rv assms(3))
  also have "... = prob_space.variance ?M f"
    unfolding 0 by simp
  also have "... \<le> (\<Sum>i\<in>I. (\<integral>x. (f (\<lambda>j. x (j, False)) - f (\<lambda>j. x (j, j = i)))^2 \<partial>?N)) / 2"
    using assms(3) by (intro efron_stein_inequality_distr prob_space_distr rv assms(1) 3) auto
  also have "... = (\<Sum>i\<in>I. expectation (\<lambda>\<omega>. (f (\<lambda>j. (\<lambda>i\<in>I\<times>UNIV. X i \<omega>) (j, False)) -
    f (\<lambda>j. (\<lambda>i\<in>I\<times>UNIV. X i \<omega>) (j, j=i)))\<^sup>2)) / 2"
    using rv unfolding 2
    by (intro sum.cong arg_cong2[where f="(/)"] integral_distr refl meas_rules) auto
  also have "... = ?R"
    by (simp add:restrict_def)
  finally show ?thesis
    by simp
qed

end