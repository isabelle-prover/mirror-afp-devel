section \<open>Definition\<close>

text \<open>This section introduces the concept of negatively associated random variables (RVs). The
definition follows, as closely as possible, the original description by
Joag-Dev and Proschan~\cite{joagdev1983}.


However, the following modifications have been made:

Singleton and empty sets of random variables are considered negatively associated. This is useful
because it simplifies many of the induction proofs. The second modification is that the RV's don't
have to be real valued.
Instead the range can be into any linearly ordered space with the borel $\sigma$-algebra. This is a
major enhancement compared to the original work, as well as results by following
authors~\cite{dubhashi2007, dubhashi1998, dubhashi1996, lisawadi2011, permantle2000}.\<close>

theory Negative_Association_Definition
  imports
    Concentration_Inequalities.Bienaymes_Identity
    Negative_Association_Util
begin

context prob_space
begin

definition neg_assoc :: "('i \<Rightarrow> 'a \<Rightarrow> 'c :: {linorder_topology}) \<Rightarrow> 'i set \<Rightarrow> bool"
  where "neg_assoc X I = (
    (\<forall>i \<in> I. random_variable borel (X i)) \<and>
    (\<forall>(f::nat \<Rightarrow> ('i \<Rightarrow> 'c) \<Rightarrow> real) J. J \<subseteq> I \<and>
      (\<forall>\<iota><2. bounded (range (f \<iota>)) \<and> mono(f \<iota>) \<and> depends_on (f \<iota>) ([J,I-J]!\<iota>) \<and>
      f \<iota> \<in> PiM ([J,I-J]!\<iota>) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel) \<longrightarrow>
      covariance (f 0 \<circ> flip X) (f 1 \<circ> flip X) \<le> 0))"

lemma neg_assocI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
  assumes "\<And>f g J. J \<subseteq> I
    \<Longrightarrow> depends_on f J \<Longrightarrow> depends_on g (I-J)
    \<Longrightarrow> mono f \<Longrightarrow> mono g
    \<Longrightarrow> bounded (range f::real set) \<Longrightarrow> bounded (range g)
    \<Longrightarrow> f \<in> PiM J (\<lambda>_. borel) \<rightarrow>\<^sub>M borel \<Longrightarrow> g \<in> PiM (I-J) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel
    \<Longrightarrow> covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0"
  shows "neg_assoc X I"
  using assms unfolding neg_assoc_def by (auto simp:numeral_eq_Suc All_less_Suc)

lemma neg_assocI2:
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
  assumes "\<And>f g J. J \<subseteq> I
    \<Longrightarrow> depends_on f J \<Longrightarrow> depends_on g (I-J)
    \<Longrightarrow> mono f \<Longrightarrow> mono g
    \<Longrightarrow> bounded (range f) \<Longrightarrow> bounded (range g)
    \<Longrightarrow> f \<in> PiM J (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)
    \<Longrightarrow> g \<in> PiM (I-J) (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)
    \<Longrightarrow> (\<integral>\<omega>. f(\<lambda>i. X i \<omega>) * g(\<lambda>i. X i \<omega>) \<partial>M)\<le>(\<integral>\<omega>. f(\<lambda>i. X i \<omega>)\<partial>M)*(\<integral>\<omega>. g(\<lambda>i. X i \<omega>) \<partial>M)"
  shows "neg_assoc X I"
proof (rule neg_assocI,goal_cases)
  case (1 i) thus ?case using assms(1) by auto
next
  case (2 f g J)

  note [measurable] = 2(8,9)
  note bounded = integrable_bounded bounded_intros

  have [measurable]: "random_variable borel (\<lambda>\<omega>. f (\<lambda>i. X i \<omega>))"
    using subsetD[OF 2(1)] by (subst depends_onD[OF 2(2)]) measurable
  moreover have [measurable]: "random_variable borel (\<lambda>\<omega>. g (\<lambda>i. X i \<omega>))"
    by (subst depends_onD[OF 2(3)]) measurable
  moreover have "integrable M (\<lambda>\<omega>. ((f \<circ> (\<lambda>x y. X y x)) \<omega>)\<^sup>2)"
    unfolding comp_def by (intro bounded bounded_subset[OF 2(6)]) auto
  moreover have "integrable M (\<lambda>\<omega>. ((g \<circ> (\<lambda>x y. X y x)) \<omega>)\<^sup>2)"
    unfolding comp_def by (intro bounded bounded_subset[OF 2(7)]) auto
  ultimately show ?case using assms(2)[OF 2(1-9)]
    by (subst covariance_eq) (auto simp:comp_def)
qed

lemma neg_assoc_empty:
  "neg_assoc X {}"
proof (intro neg_assocI2, goal_cases)
  case (1 i)
  then show ?case by simp
next
  case (2 f g J)
  define fc gc where fc:"fc = f undefined" and gc:"gc = g undefined"

  have "depends_on f {}" "depends_on g {}" using 2 by auto
  hence fg_simps: "f = (\<lambda>x. fc)" "g = (\<lambda>x. gc)" unfolding fc gc using depends_on_empty by auto
  then show ?case unfolding fg_simps by (simp add:prob_space)
qed

lemma neg_assoc_singleton:
  assumes "random_variable borel (X i)"
  shows "neg_assoc X {i}"
proof (rule neg_assocI2, goal_cases)
  case (1 i)
  then show ?case using assms by auto
next
  case (2 f g J)
  show ?case
  proof (cases "J = {}")
    case True
    define fc where "fc = f undefined"
    have f:"f = (\<lambda>_. fc)"
      unfolding fc_def by (intro ext depends_onD2[OF 2(2)]) (auto simp:True)
    then show ?thesis unfolding f by (simp add:prob_space)
  next
    case False
    hence J: "J = {i}" using 2(1) by auto
    define gc where "gc = g undefined"
    have g:"g = (\<lambda>_. gc)"
      unfolding gc_def by (intro ext depends_onD2[OF 2(3)]) (auto simp:J)
    then show ?thesis unfolding g by (simp add:prob_space)
  qed
qed

lemma neg_assoc_imp_measurable:
  assumes "neg_assoc X I"
  assumes "i \<in> I"
  shows "random_variable borel (X i)"
  using assms unfolding neg_assoc_def by auto

text \<open>Even though the assumption was that defining property is true for pairs of monotone functions
over the random variables, it is also true for pairs of anti-monotone functions.\<close>

lemma neg_assoc_imp_mult_mono_bounded:
  fixes f g :: "('i \<Rightarrow> 'c::linorder_topology) \<Rightarrow> real"
  assumes "neg_assoc X I"
  assumes "J \<subseteq> I"
  assumes "bounded (range f)" "bounded (range g)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g"
  assumes "depends_on f J" "depends_on g (I-J)"
  assumes [measurable]: "f \<in> borel_measurable (Pi\<^sub>M J (\<lambda>_. borel))"
  assumes [measurable]: "g \<in> borel_measurable (Pi\<^sub>M (I-J) (\<lambda>_. borel))"
  shows
    "covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0"
    "(\<integral>\<omega>. f (\<lambda>i. X i \<omega>) * g (\<lambda>i. X i \<omega>) \<partial>M) \<le> expectation (\<lambda>x. f(\<lambda>y. X y x)) * expectation (\<lambda>x. g(\<lambda>y. X y x))"
      (is "?L \<le> ?R")
proof -
  define q where "q \<iota> = (if \<iota> = 0 then f else g)" for \<iota> :: nat
  define h where "h \<iota> = ((*) (\<plusminus>\<^bsub>\<eta>\<^esub>)) \<circ> (q \<iota>)" for \<iota> :: nat

  note [measurable] = neg_assoc_imp_measurable[OF assms(1)]
  note bounded = integrable_bounded bounded_intros

  have 1:"bounded (range ((*) (\<plusminus>\<^bsub>\<eta>\<^esub>) \<circ> q \<iota>))" "depends_on (q \<iota>) ([J,I-J]!\<iota>)"
    "q \<iota> \<in> PiM ([J,I-J]!\<iota>) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel" "mono ((*) (\<plusminus>\<^bsub>\<eta>\<^esub>) \<circ> q \<iota>)" if "\<iota> \<in> {0,1}" for \<iota>
    using that assms unfolding q_def conv_rel_to_sign by (auto intro:bounded_mult_comp)

  have 2: "((*) (\<plusminus>\<^bsub>\<eta>\<^esub>::real)) \<in> borel \<rightarrow>\<^sub>M borel" by simp

  have 3:"\<forall>\<iota><Suc (Suc 0). bounded (range (h \<iota>))\<and>mono(h \<iota>) \<and> depends_on (h \<iota>) ([J,I-J]!\<iota>) \<and>
    h \<iota> \<in> PiM ([J,I-J]!\<iota>) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel" unfolding All_less_Suc h_def
    by (intro conjI 1 depends_on_comp measurable_comp[OF _ 2]) auto

  have "covariance (f \<circ> flip X) (g \<circ> flip X) = covariance (q 0 \<circ> flip X) (q 1 \<circ> flip X)"
    unfolding q_def by simp
  also have "\<dots> = covariance (h 0 \<circ> flip X) (h 1 \<circ> flip X)"
    unfolding h_def covariance_def comp_def by (cases \<eta>) (auto simp:algebra_simps)
  also have "... \<le> 0" using 3 assms(1,2) numeral_2_eq_2 unfolding neg_assoc_def by metis
  finally show "covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0" by simp

  moreover have m_f: "random_variable borel (\<lambda>x. f(\<lambda>i. X i x))"
    using subsetD[OF assms(2)] by (subst depends_onD[OF assms(7)]) measurable
  moreover have m_g: "random_variable borel (\<lambda>x. g(\<lambda>i. X i x))"
    by (subst depends_onD[OF assms(8)]) measurable
  moreover have "integrable M (\<lambda>\<omega>. ((f \<circ> (\<lambda>x y. X y x)) \<omega>)\<^sup>2)" unfolding comp_def
    by (intro bounded bounded_subset[OF assms(3)] measurable_compose[OF m_f]) auto
  moreover have "integrable M (\<lambda>\<omega>. ((g \<circ> (\<lambda>x y. X y x)) \<omega>)\<^sup>2)" unfolding comp_def
    by (intro bounded bounded_subset[OF assms(4)] measurable_compose[OF m_g]) auto

  ultimately show  "?L \<le> ?R" by (subst (asm) covariance_eq) (auto simp:comp_def)
qed

lemma lim_min_n: "(\<lambda>n. min (real n) x) \<longlonglongrightarrow> x"
proof -
  define m where "m = nat \<lceil>x\<rceil>"
  have "min (real (n+m)) x = x" for n unfolding m_def by (intro min_absorb2) linarith
  hence "(\<lambda>n. min (real (n+m)) x) \<longlonglongrightarrow> x" by simp
  thus ?thesis using LIMSEQ_offset[where k="m"] by fast
qed

lemma lim_clamp_n: "(\<lambda>n. clamp (-real n) (real n) x) \<longlonglongrightarrow> x"
proof -
  define m where "m = nat \<lceil>\<bar>x\<bar>\<rceil>"
  have "clamp (-real (n+m)) (real (n+m)) x = x" for n unfolding m_def
    by (intro clamp_eqI[symmetric]) linarith
  hence "(\<lambda>n. clamp (-real (n+m)) (real (n+m)) x) \<longlonglongrightarrow> x" by simp
  thus ?thesis using LIMSEQ_offset[where k="m"] by fast
qed

lemma neg_assoc_imp_mult_mono:
  fixes f g :: "('i \<Rightarrow> 'c::linorder_topology) \<Rightarrow> real"
  assumes "neg_assoc X I"
  assumes "J \<subseteq> I"
  assumes "square_integrable M (f \<circ> flip X)" "square_integrable M (g \<circ> flip X)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g"
  assumes "depends_on f J" "depends_on g (I-J)"
  assumes [measurable]: "f \<in> borel_measurable (Pi\<^sub>M J (\<lambda>_. borel))"
  assumes [measurable]: "g \<in> borel_measurable (Pi\<^sub>M (I-J) (\<lambda>_. borel))"
    shows "(\<integral>\<omega>. f (\<lambda>i. X i \<omega>) * g (\<lambda>i. X i \<omega>) \<partial>M) \<le> (\<integral>x. f(\<lambda>y. X y x)\<partial>M) * (\<integral>x. g(\<lambda>y. X y x)\<partial>M)"
      (is "?L \<le> ?R")
proof -
  let ?cf = "\<lambda>n x. clamp (-real n) (real n) (f x)"
  let ?cg = "\<lambda>n x. clamp (-real n) (real n) (g x)"

  note [measurable] = neg_assoc_imp_measurable[OF assms(1)]

  have m_f: "random_variable borel (\<lambda>x. f(\<lambda>i. X i x))"
    using subsetD[OF assms(2)] by (subst depends_onD[OF assms(7)]) measurable

  have m_g: "random_variable borel (\<lambda>x. g(\<lambda>i. X i x))"
    by (subst depends_onD[OF assms(8)]) measurable

  note intro_rules = borel_measurable_times measurable_compose[OF _ clamp_borel] AE_I2
    measurable_compose[OF _ borel_measurable_norm] lim_clamp_n m_f m_g

  have a: "(\<lambda>n. (\<integral>\<omega>. ?cf n (\<lambda>i. X i \<omega>) * ?cg n (\<lambda>i. X i \<omega>) \<partial>M)) \<longlonglongrightarrow> ?L" using assms(3,4)
    by (intro integral_dominated_convergence[where w="\<lambda>\<omega>. norm (f(\<lambda>i. X i \<omega>))*norm (g(\<lambda>i. X i \<omega>))"]
        intro_rules tendsto_mult cauchy_schwartz(1)[where M="M"])
       (auto intro!: clamp_abs_le mult_mono simp add:comp_def abs_mult)

  have "(\<lambda>n. (\<integral>x. ?cf n (\<lambda>y. X y x)\<partial>M)) \<longlonglongrightarrow> (\<integral>x. f(\<lambda>y. X y x)\<partial>M)"
    using square_integrable_imp_integrable[OF m_f] assms(3) unfolding comp_def
    by (intro integral_dominated_convergence[where w = "\<lambda>\<omega>. norm (f(\<lambda>i. X i \<omega>))"] intro_rules)
      (simp_all add:clamp_abs_le)

  moreover have "(\<lambda>n. (\<integral>x. ?cg n (\<lambda>y. X y x)\<partial>M)) \<longlonglongrightarrow> (\<integral>x. g(\<lambda>y. X y x)\<partial>M)"
    using square_integrable_imp_integrable[OF m_g] assms(4) unfolding comp_def
    by (intro integral_dominated_convergence[where w = "\<lambda>\<omega>. norm (g(\<lambda>i. X i \<omega>))"] intro_rules)
      (simp_all add:clamp_abs_le)

  ultimately have b: "(\<lambda>n. (\<integral>x. ?cf n (\<lambda>y. X y x)\<partial>M) * (\<integral>x. ?cg n (\<lambda>y. X y x) \<partial>M)) \<longlonglongrightarrow> ?R"
    by (rule tendsto_mult)

  show ?thesis
    by (intro lim_mono[OF _ a b, where N="0"] bounded_clamp_alt assms(5,6,9,10) monotone_clamp
        neg_assoc_imp_mult_mono_bounded[OF assms(1,2), where \<eta>="\<eta>"] depends_on_comp_2[OF assms(7)]
        measurable_compose[OF _ clamp_borel] depends_on_comp_2[OF assms(8)])
qed

text \<open>Property P4~\cite{joagdev1983}\<close>
lemma neg_assoc_subset:
  assumes "J \<subseteq> I"
  assumes "neg_assoc X I"
  shows "neg_assoc X J"
proof (rule neg_assocI,goal_cases)
  case (1 i)
  then show ?case using neg_assoc_imp_measurable[OF assms(2)] assms(1) by auto
next
  case (2 f g K)
  have a:"K \<subseteq> I" using 2 assms(1) by auto

  have "g = g \<circ> (\<lambda>m. restrict m (J-K))"
    using 2 depends_onD unfolding comp_def by (intro ext) auto
  also have "... \<in> borel_measurable (Pi\<^sub>M (I - K) (\<lambda>_. borel))"
    using 2 assms(1) by (intro measurable_comp[OF measurable_restrict_subset]) auto
  finally have "g \<in> borel_measurable (Pi\<^sub>M (I - K) (\<lambda>_. borel))" by simp
  moreover have "depends_on g (I-K)" using depends_on_mono assms(1) 2
    by (metis Diff_mono dual_order.eq_iff)
  ultimately show "covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0"
    using 2 by (intro neg_assoc_imp_mult_mono_bounded[OF assms(2) a, where \<eta>="Fwd"]) simp_all
qed

lemma neg_assoc_imp_mult_mono_nonneg:
  fixes f g :: "('i \<Rightarrow> 'c::linorder_topology) \<Rightarrow> real"
  assumes "neg_assoc X I" "J \<subseteq> I"
  assumes "range f \<subseteq> {0..}" "range g \<subseteq> {0..}"
  assumes "integrable M (f \<circ> flip X)" "integrable M (g \<circ> flip X)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g"
  assumes "depends_on f J" "depends_on g (I-J)"
  assumes "f \<in> borel_measurable (Pi\<^sub>M J (\<lambda>_. borel))" "g \<in> borel_measurable (Pi\<^sub>M (I-J) (\<lambda>_. borel))"
  shows "has_int_that M (\<lambda>\<omega>. f (flip X \<omega>) * g (flip X \<omega>))
    (\<lambda>r. r \<le> expectation (f \<circ> flip X) * expectation (g \<circ> flip X))"
proof -
  let ?cf = "(\<lambda>n x. min (real n) (f x))"
  let ?cg = "(\<lambda>n x. min (real n) (g x))"

  define u where "u = (\<lambda>\<omega>. f (\<lambda>i. X i \<omega>) * g (\<lambda>i. X i \<omega>))"
  define h where "h n \<omega> = ?cf n  (\<lambda>i. X i \<omega>) * ?cg n (\<lambda>i. X i \<omega>)" for n \<omega>
  define x where "x = (SUP n. expectation (h n))"

  note borel_intros = borel_measurable_times borel_measurable_const borel_measurable_min
    borel_measurable_power
  note bounded_intros' = integrable_bounded bounded_intros bounded_const_min

  have f_meas: "random_variable borel (\<lambda>x. f (\<lambda>i. X i x))"
    using borel_measurable_integrable[OF assms(5)] by (simp add:comp_def)
  have g_meas: "random_variable borel (\<lambda>x. g (\<lambda>i. X i x))"
    using borel_measurable_integrable[OF assms(6)] by (simp add:comp_def)

  have h_int: "integrable M (h n)" for n
    unfolding h_def using assms(3,4) by (intro bounded_intros' borel_intros f_meas g_meas) fast+

  have exp_h_le_R: "expectation (h n) \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X)" for n
  proof -
    have "square_integrable M ((\<lambda>a. min (real n) (f a)) \<circ> (\<lambda>x y. X y x))"
      using assms(3) unfolding comp_def
      by (intro bounded_intros' bdd_belowI[where m="0"] borel_intros f_meas) auto
    moreover have "square_integrable M ((\<lambda>a. min (real n) (g a)) \<circ> (\<lambda>x y. X y x))"
      using assms(4) unfolding comp_def
      by (intro bounded_intros' bdd_belowI[where m="0"] borel_intros g_meas) auto
    moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) ((\<lambda>a. min (real n) (f a)))"
      using monotoneD[OF assms(7)] unfolding comp_def min_mult_distrib_left
      by (intro monotoneI) (cases "\<eta>", fastforce+)
    moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) ((\<lambda>a. min (real n) (g a)))"
      using monotoneD[OF assms(8)] unfolding comp_def min_mult_distrib_left
      by (intro monotoneI) (cases \<eta>, fastforce+)
    ultimately have "expectation (h n) \<le> expectation (?cf n\<circ>flip X) * expectation (?cg n\<circ>flip X)"
      unfolding h_def comp_def
      by (intro neg_assoc_imp_mult_mono[OF assms(1-2)] borel_intros assms(11,12)
          depends_on_comp_2[OF assms(10)] depends_on_comp_2[OF assms(9)]) (auto simp:comp_def)
    also have "... \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X)"
      using assms(3,4) by (intro mult_mono integral_nonneg_AE AE_I2 integral_mono' assms(5,6)) auto
    finally show ?thesis by simp
  qed

  have h_mono_ptw: "AE \<omega> in M. mono (\<lambda>n. h n \<omega>)"
    using assms(3,4) unfolding h_def by (intro AE_I2 monoI mult_mono) auto
  have h_mono: "mono (\<lambda>n. expectation (h n))"
    by (intro monoI integral_mono_AE AE_mp[OF h_mono_ptw AE_I2] h_int) (simp add:mono_def)

  have "random_variable borel u" using f_meas g_meas unfolding u_def by (intro borel_intros)
  moreover have "AE \<omega> in M. (\<lambda>n. h n \<omega>) \<longlonglongrightarrow> u \<omega>"
    unfolding h_def u_def by (intro tendsto_mult lim_min_n AE_I2)
  moreover have "bdd_above (range (\<lambda>n. expectation (h n)))"
    using exp_h_le_R by (intro bdd_aboveI) auto
  hence "(\<lambda>n. expectation (h n)) \<longlonglongrightarrow> x"
    using LIMSEQ_incseq_SUP[OF _ h_mono] unfolding x_def by simp
  ultimately have "has_bochner_integral M u x" using h_int h_mono_ptw
    by (intro has_bochner_integral_monotone_convergence[where f="h"])
  moreover have "x \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X)"
    unfolding x_def by (intro cSUP_least exp_h_le_R) simp
  ultimately show ?thesis unfolding has_bochner_integral_iff u_def has_int_that_def by auto
qed

text \<open>Property P2~\cite{joagdev1983}\<close>
lemma neg_assoc_imp_prod_mono:
  fixes f :: "'i \<Rightarrow> ('c::linorder_topology) \<Rightarrow> real"
  assumes "finite I"
  assumes "neg_assoc X I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i (X i \<omega>))"
  assumes "\<And>i. i \<in> I \<Longrightarrow> monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> range (f i)\<subseteq>{0..}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable borel"
  shows "has_int_that M (\<lambda>\<omega>. (\<Prod>i\<in>I. f i (X i \<omega>))) (\<lambda>r. r\<le>(\<Prod>i\<in> I. expectation (\<lambda>\<omega>. f i (X i \<omega>))))"
  using assms
proof (induction I rule:finite_induct)
  case empty then show ?case by (simp add:has_int_that_def)
next
  case (insert x F)

  define g where "g v = f x (v x)" for v
  define h where "h v = (\<Prod>i\<in>F. f i (v i))" for v

  have 0: "{x} \<subseteq> insert x F" by auto

  have ran_g: "range g \<subseteq> {0..}" using insert(7) unfolding g_def by auto

  have "True = has_int_that M (\<lambda>\<omega>. \<Prod>i\<in>F. f i(X i \<omega>)) (\<lambda>r. r\<le>(\<Prod>i\<in>F. expectation(\<lambda>\<omega>. f i(X i \<omega>))))"
    by (intro true_eq_iff insert neg_assoc_subset[OF _ insert(4)]) auto
  also have "... = has_int_that M (h \<circ> flip X) (\<lambda>r. r \<le> (\<Prod>i\<in>F. expectation (\<lambda>\<omega>. f i (X i \<omega>))))"
    unfolding h_def by (intro arg_cong2[where f="has_int_that M"] refl)(simp add:comp_def)
  finally have 2: "has_int_that M (h \<circ> flip X) (\<lambda>r. r \<le> (\<Prod>i\<in>F. expectation (\<lambda>\<omega>. f i (X i \<omega>))))"
    by simp

  have "(\<Prod>i\<in>F. f i (v i)) \<ge> 0" for v using insert(7) by (intro prod_nonneg) auto
  hence "range h \<subseteq> {0..}" unfolding h_def by auto
  moreover have "integrable M (g \<circ> flip X)" unfolding g_def using insert(5) by (auto simp:comp_def)
  moreover have 3:"monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f x)" using insert(6) by simp
  have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g" using monotoneD[OF 3]
    unfolding g_def by (intro monotoneI) (auto simp:comp_def le_fun_def)
  moreover have 4:"monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f i)" "\<And>x. f i x \<ge> 0" if "i \<in> F" for i
    using that insert(6,7) by force+
  hence "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) h" using monotoneD[OF 4(1)] unfolding h_def
    by (intro monotoneI) (cases \<eta>, auto intro:prod_mono simp:comp_def le_fun_def)
  moreover have "depends_on g {x}" unfolding g_def by (intro depends_onI) force
  moreover have "depends_on h F"
    unfolding h_def by (intro depends_onI prod.cong refl) force
  hence "depends_on h (F - {x})" using insert(2) by simp
  moreover have "g \<in> borel_measurable (Pi\<^sub>M {x} (\<lambda>_. borel))" unfolding g_def
    by (intro measurable_compose[OF _ insert(8)] measurable_component_singleton) auto
  moreover have "h \<in> borel_measurable (Pi\<^sub>M F (\<lambda>_. borel))"
    unfolding h_def by (intro borel_measurable_prod measurable_compose[OF _ insert(8)]
        measurable_component_singleton) auto
  hence "h \<in> borel_measurable (Pi\<^sub>M (F - {x}) (\<lambda>_. borel))" using insert(2) by simp
  ultimately have "True = has_int_that M (\<lambda>\<omega>. g (flip X \<omega>) * h (flip X \<omega>))
    (\<lambda>r. r \<le> expectation (g \<circ> flip X) * expectation (h \<circ> flip X))"
    by (intro true_eq_iff neg_assoc_imp_mult_mono_nonneg[OF insert(4) 0, where \<eta>="\<eta>"]
        ran_g has_int_thatD[OF 2]) simp_all
  also have "\<dots> = has_int_that M (\<lambda>\<omega>. (\<Prod>i\<in>insert x F. f i (X i \<omega>)))
    (\<lambda>r. r \<le> expectation (g \<circ> flip X) * expectation (h \<circ> flip X))"
    unfolding g_def h_def using insert(1,2) by (intro arg_cong2[where f="has_int_that M"] refl) simp
  also have "\<dots> \<le> has_int_that M (\<lambda>\<omega>. (\<Prod>i\<in>insert x F. f i (X i \<omega>)))
    (\<lambda>r. r \<le> expectation (g \<circ> flip X) * (\<Prod>i \<in> F. expectation (f i \<circ> X i)))"
    using ran_g has_int_thatD[OF 2] by (intro has_int_that_mono le_trans mult_left_mono
        integral_nonneg_AE AE_I2) (auto simp: comp_def)
  also have "\<dots> = has_int_that M
    (\<lambda>\<omega>. \<Prod>i\<in>insert x F. f i (X i \<omega>)) (\<lambda>r. r \<le> (\<Prod>i\<in>insert x F. expectation (f i \<circ> X i)))"
    using insert(1,2) by (intro arg_cong2[where f="has_int_that M"] refl) (simp add:g_def comp_def)
  finally show ?case using le_boolE by (simp add:comp_def)
qed

text \<open>Property P5~\cite{joagdev1983}\<close>
lemma neg_assoc_compose:
  fixes f :: "'j \<Rightarrow> ('i \<Rightarrow> ('c::linorder_topology)) \<Rightarrow> ('d ::linorder_topology)"
  assumes "finite I"
  assumes "neg_assoc X I"
  assumes "\<And>j. j \<in> J \<Longrightarrow> deps j \<subseteq> I"
  assumes "\<And>j1 j2. j1 \<in> J \<Longrightarrow> j2 \<in> J \<Longrightarrow> j1 \<noteq> j2 \<Longrightarrow> deps j1 \<inter> deps j2 = {}"
  assumes "\<And>j. j \<in> J \<Longrightarrow> monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f j)"
  assumes "\<And>j. j \<in> J \<Longrightarrow> depends_on (f j) (deps j)"
  assumes "\<And>j. j \<in> J \<Longrightarrow> f j \<in> borel_measurable (PiM (deps j) (\<lambda>_. borel))"
  shows "neg_assoc (\<lambda>j \<omega>. f j (\<lambda>i. X i \<omega>)) J"
proof (rule neg_assocI, goal_cases)
  case (1 i)
  note [measurable] = neg_assoc_imp_measurable[OF assms(2)] assms(7)[OF 1]
  note 3 = assms(3)[OF 1]
  have 2: "f i (\<lambda>i. X i \<omega>) = f i (\<lambda>i\<in>deps i. X i \<omega>)" for \<omega>
    using 3 by (intro depends_onD2[OF assms(6)] 1) fastforce
  show ?case unfolding 2 by measurable (rule subsetD[OF 3])
next
  case (2 g h K)

  let ?g = "(\<lambda>\<omega>. g (\<lambda>j. f j \<omega>))"
  let ?h = "(\<lambda>\<omega>. h (\<lambda>j. f j \<omega>))"

  note dep_f = depends_onD[OF depends_on_mono[OF _ assms(6)],symmetric]

  have g_alt_1: "?g = (\<lambda>\<omega>. g (\<lambda>j \<in> J. f j \<omega>))"
    using 2(1) by (intro ext depends_onD[OF depends_on_mono[OF _ 2(2)]]) auto
  have g_alt_2: "?g = (\<lambda>\<omega>. g (\<lambda>j \<in> K. f j \<omega>))"
    by (intro ext depends_onD[OF 2(2)])
  have g_alt_3: "?g = (\<lambda>\<omega>. g (\<lambda>j \<in> K. f j (restrict \<omega> (deps j))))" unfolding g_alt_2 using 2(1)
    by (intro restrict_ext ext arg_cong[where f="g"] depends_onD[OF assms(6)]) auto

  have h_alt_1: "?h = (\<lambda>\<omega>. h (\<lambda>j \<in> J. f j \<omega>))"
    by (intro ext depends_onD[OF depends_on_mono[OF _ 2(3)]]) auto
  have h_alt_2: "?h = (\<lambda>\<omega>. h (\<lambda>j \<in> J-K. f j \<omega>))"
    by (intro ext depends_onD[OF 2(3)])
  have h_alt_3: "?h = (\<lambda>\<omega>. h (\<lambda>j \<in> J-K. f j (restrict \<omega> (deps j))))" unfolding h_alt_2
    by (intro restrict_ext ext arg_cong[where f="h"] depends_onD[OF assms(6)]) auto

  have 3: "\<Union> (deps ` (J-K)) \<subseteq> I - \<Union> (deps ` K)" using assms(3,4) 2(1) by blast

  have "\<Union> (deps ` K) \<subseteq> I" using 2(1) assms(3) by auto
  moreover have "bounded (range ?g)" "bounded (range ?h)"
    using 2(6,7) by (auto intro: bounded_subset)
  moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) ?g"
    unfolding g_alt_1 using monotoneD[OF assms(5)]
    by (intro monotoneI) (cases \<eta>, auto intro!:monoD[OF 2(4)] le_funI)
  moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) ?h"
    unfolding h_alt_1 using monotoneD[OF assms(5)]
    by (intro monotoneI) (cases \<eta>, auto intro!:monoD[OF 2(5)] le_funI)
  moreover have "depends_on ?g (\<Union> (deps ` K))"
    using 2(1) unfolding g_alt_2
    by (intro depends_onI arg_cong[where f="g"] restrict_ext depends_onD2[OF assms(6)]) auto
  moreover have "depends_on ?h (\<Union> (deps ` (J-K)))"
    unfolding h_alt_2
    by (intro depends_onI arg_cong[where f="h"] restrict_ext depends_onD2[OF assms(6)]) auto
  hence "depends_on ?h (I - \<Union> (deps ` K))" using depends_on_mono[OF 3] by auto
  moreover have "?g \<in> borel_measurable (Pi\<^sub>M (\<Union> (deps ` K)) (\<lambda>_. borel))"
    unfolding g_alt_3 using 2(1)
    by (intro measurable_compose[OF _ 2(8)] measurable_compose[OF _ assms(7)]
        measurable_restrict measurable_component_singleton) auto
  moreover have "?h \<in> borel_measurable (Pi\<^sub>M (I - \<Union> (deps ` K)) (\<lambda>_. borel))"
    unfolding h_alt_3 using 3
    by (intro measurable_compose[OF _ 2(9)] measurable_compose[OF _ assms(7)] measurable_restrict
        measurable_component_singleton) auto
  ultimately have "covariance (?g \<circ> flip X) (?h \<circ> flip X) \<le> 0"
    by (rule neg_assoc_imp_mult_mono_bounded[OF assms(2), where J="\<Union>(deps ` K)" and \<eta>="\<eta>"])
  thus "covariance (g \<circ> (\<lambda>x y. f y (\<lambda>i. X i x))) (h \<circ> (\<lambda>x y. f y (\<lambda>i. X i x))) \<le> 0"
    by (simp add:comp_def)
qed

lemma neg_assoc_compose_simple:
  fixes f :: "'i \<Rightarrow> ('c::linorder_topology) \<Rightarrow> ('d ::linorder_topology)"
  assumes "finite I"
  assumes "neg_assoc X I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f i)"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable borel"
  shows "neg_assoc (\<lambda>i \<omega>. f i (X i \<omega>)) I"
proof -
  have "depends_on (\<lambda>\<omega>. f i (\<omega> i)) {i}" if "i \<in> I" for i
    by (intro depends_onI) auto
  moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (\<lambda>\<omega>. f i (\<omega> i))" if "i \<in> I" for i
    using monotoneD[OF assms(3)[OF that]] by (intro monotoneI) (cases \<eta>, auto dest:le_funE)
  ultimately show ?thesis
    by (intro neg_assoc_compose[OF assms(1,2), where deps="\<lambda>i. {i}" and \<eta>="\<eta>"]) simp_all
qed

lemma covariance_distr:
  fixes f g :: "'b \<Rightarrow> real"
  assumes [measurable]: "\<phi> \<in> M \<rightarrow>\<^sub>M N"  "f \<in> borel_measurable N"  "g \<in> borel_measurable N"
  shows "prob_space.covariance (distr M N \<phi>) f g = covariance (f \<circ> \<phi>) (g \<circ> \<phi>)" (is "?L = ?R")
proof -
  let ?M' = "distr M N \<phi>"
  have ps_distr: "prob_space ?M'" by (intro prob_space_distr) measurable
  interpret p2: prob_space ?M'
    using ps_distr by auto
  have "?L = expectation (\<lambda>x. (f(\<phi> x)-expectation (\<lambda>x. f(\<phi> x)))*(g(\<phi> x)-expectation (\<lambda>x. g(\<phi> x))))"
    unfolding p2.covariance_def by (subst (1 2 3) integral_distr) measurable
  also have "\<dots> = ?R"
    unfolding covariance_def comp_def by simp
  finally show ?thesis by simp
qed

lemma neg_assoc_iff_distr:
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> borel_measurable M"
  shows "neg_assoc X I \<longleftrightarrow>
    prob_space.neg_assoc (distr M (PiM I (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) (flip id) I"
    (is "?L \<longleftrightarrow> ?R")
proof
  let ?M' = "distr M (Pi\<^sub>M I (\<lambda>_. borel))  (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)"
  have ps_distr: "prob_space ?M'"
    by (intro prob_space_distr) measurable

  interpret p2: prob_space ?M'
    using ps_distr by auto

  show "?R" if "?L"
  proof (rule p2.neg_assocI, goal_cases)
    case (1 i)
    thus ?case using assms that unfolding id_def by measurable
  next
    case (2 f g J)

    have dep_I: "depends_on f I" "depends_on g I"
      using depends_on_mono[OF Diff_subset[of I J]] depends_on_mono[OF 2(1)] 2(2-3) by auto

    have f_meas[measurable]: "(\<lambda>x. f x) \<in> borel_measurable (Pi\<^sub>M I (\<lambda>_. borel))"
      by (subst depends_onD[OF 2(2)]) (intro 2 measurable_compose[OF measurable_restrict_subset])

    have g_meas[measurable]: "(\<lambda>x. g x) \<in> borel_measurable (Pi\<^sub>M I (\<lambda>_. borel))"
      by (subst depends_onD[OF 2(3)])
        (intro 2 measurable_compose[OF measurable_restrict_subset], auto)

    have "covariance (f \<circ> id \<circ> (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) (g \<circ> id \<circ> (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) =
      covariance (f \<circ> flip X) (g \<circ> flip X)"
      using depends_onD[OF dep_I(2)] depends_onD[OF dep_I(1)] by (simp add:comp_def)
    also have "\<dots> \<le> 0"
      using 2 by (intro neg_assoc_imp_mult_mono_bounded[OF that 2(1,6,7), where \<eta>="Fwd"]) simp_all
    finally have "covariance (f \<circ> id \<circ> (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) (g \<circ> id \<circ> (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) \<le> 0" by simp
    thus ?case by (subst covariance_distr) measurable
  qed

  show "?L" if "?R"
  proof (rule neg_assocI, goal_cases)
    case (1 i)
    then show ?case by measurable
  next
    case (2 f g J)

    have dep_I: "depends_on f I" "depends_on g I"
      using depends_on_mono[OF Diff_subset[of I J]] depends_on_mono[OF 2(1)] 2(2-3) by auto

    have f_meas[measurable]: "(\<lambda>x. f x) \<in> borel_measurable (Pi\<^sub>M I (\<lambda>_. borel))"
      by (subst depends_onD[OF 2(2)]) (intro 2 measurable_compose[OF measurable_restrict_subset])

    have g_meas[measurable]: "(\<lambda>x. g x) \<in> borel_measurable (Pi\<^sub>M I (\<lambda>_. borel))"
      by (subst depends_onD[OF 2(3)])
        (intro 2 measurable_compose[OF measurable_restrict_subset], auto)

    note [measurable] = 2(8,9)
    have "covariance (f \<circ> (\<lambda>x y. X y x)) (g \<circ> (\<lambda>x y. X y x)) =
      covariance (f \<circ> (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) (g \<circ> (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>))"
      using depends_onD[OF dep_I(2)] depends_onD[OF dep_I(1)] by (simp add:comp_def)
    also have "\<dots> =  p2.covariance (f \<circ> id) (g \<circ> id)" by (subst covariance_distr) measurable
    also have "\<dots> \<le> 0"
      using 2 by (intro p2.neg_assoc_imp_mult_mono_bounded[OF that 2(1), where \<eta>="Fwd"])
        (simp_all add:comp_def)
    finally show ?case by simp
  qed
qed

lemma neg_assoc_cong:
  assumes "finite I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> borel_measurable M"
  assumes "neg_assoc X I" "\<And>i. i \<in> I \<Longrightarrow> AE \<omega> in M. X i \<omega> = Y i \<omega>"
  shows "neg_assoc Y I"
proof -
  have [measurable]: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> borel_measurable M"
    using neg_assoc_imp_measurable[OF assms(3)] by auto

  let ?B = "(\<lambda>_. borel)"
  have a:"AE x in M. (\<forall>i\<in>I. (X i x = Y i x))" by (intro AE_finite_allI assms)
  have "AE x in M. (\<lambda>i\<in>I. X i x) = (\<lambda>i\<in>I. Y i x)" by (intro AE_mp[OF a AE_I2]) auto
  hence b:"distr M (PiM I ?B) (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>) = distr M (PiM I ?B) (\<lambda>\<omega>. \<lambda>i\<in>I. Y i \<omega>)"
    by (intro distr_cong_AE refl) measurable
  have "prob_space.neg_assoc (distr M (PiM I (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)) (flip id) I"
    using assms(2,3) by (intro iffD1[OF neg_assoc_iff_distr]) measurable
  thus ?thesis unfolding b using assms(2)
    by (intro iffD2[OF neg_assoc_iff_distr[where I="I"]])  auto
qed

lemma neg_assoc_reindex_aux:
  assumes "inj_on h I"
  assumes "neg_assoc X (h ` I)"
  shows "neg_assoc (\<lambda>k. X (h k)) I"
proof (rule neg_assocI, goal_cases)
  case (1 i) thus ?case using neg_assoc_imp_measurable[OF assms(2)] by simp
next
  case (2 f g J)
  let ?f = "(\<lambda>\<omega>. f (compose J \<omega> h))"
  let ?g = "(\<lambda>\<omega>. g (compose (I-J) \<omega> h))"

  note neg_assoc_imp_mult_mono_intros =
    neg_assoc_imp_mult_mono_bounded(1)[OF assms(2), where J="h`J" and \<eta>="Fwd"]
    measurable_compose[OF _ 2(8)] measurable_compose[OF _ 2(9)]
    measurable_compose[OF _ measurable_finmap_compose]
    bounded_range_imp[OF 2(6)] bounded_range_imp[OF 2(7)]

  have [simp]:"h ` I - h ` J =  h ` (I-J)"
    using assms(1) 2(1) by (simp add: inj_on_image_set_diff)

  have "covariance (f\<circ>(\<lambda>x y. X(h y)x)) (g\<circ>(\<lambda>x y. X(h y)x)) = covariance (?f \<circ> flip X) (?g \<circ> flip X)"
    unfolding comp_def
    by (intro arg_cong2[where f="covariance"] ext depends_onD2[OF 2(2)] depends_onD2[OF 2(3)])
     (auto simp:compose_def)
  also have "\<dots> \<le> 0" using 2(1)
    by (intro neg_assoc_imp_mult_mono_intros monotoneI depends_onI) (auto intro!:
        monoD[OF 2(4)] monoD[OF 2(5)] simp:le_fun_def compose_def restrict_def cong:if_cong)
  finally show ?case by simp
qed

lemma neg_assoc_reindex:
  assumes "inj_on h I" "finite I"
  shows "neg_assoc X (h ` I) \<longleftrightarrow> neg_assoc (\<lambda>k. X (h k)) I" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  thus ?R using neg_assoc_reindex_aux[OF assms(1)] by blast
next
  note inv_h_inj = inj_on_the_inv_into[OF assms(1)]
  assume a:?R
  hence b:"neg_assoc (\<lambda>k. X (h (the_inv_into I h k))) (h ` I)"
    using the_inv_into_onto[OF assms(1)] by (intro neg_assoc_reindex_aux[OF inv_h_inj]) auto
  show ?L
    using f_the_inv_into_f[OF assms(1)] neg_assoc_imp_measurable[OF a] assms(2)
    by (intro neg_assoc_cong[OF _ _ b]) auto
qed

lemma measurable_compose_merge_1:
  assumes "depends_on h K"
  assumes "h \<in> PiM K M' \<rightarrow>\<^sub>M N" "K \<subseteq> I \<union> J"
  assumes "(\<lambda>x. restrict (fst (f x)) (K \<inter> I)) \<in> A \<rightarrow>\<^sub>M PiM (K \<inter> I) M'"
  assumes "(\<lambda>x. restrict (snd (f x)) (K \<inter> J)) \<in> A \<rightarrow>\<^sub>M PiM (K \<inter> J) M'"
  shows "(\<lambda>x. h(merge I J (f x))) \<in> A \<rightarrow>\<^sub>M N"
proof -
  let ?f1 = "\<lambda>x. fst (f x)"
  let ?f2 = "\<lambda>x. snd (f x)"
  let ?g1 = "\<lambda>x. restrict (fst (f x)) (K \<inter> I)"
  let ?g2 = "\<lambda>x. restrict (snd (f x)) (K \<inter> J)"

  have a1:"(\<lambda>x. merge I J (?g1 x, ?g2 x) i) \<in> A \<rightarrow>\<^sub>M M' i" if "i \<in> K \<inter> I" for i
    using that measurable_compose[OF assms(4) measurable_component_singleton[OF that]]
    by (simp add:merge_def)

  have a2:"(\<lambda>x. merge I J (?g1 x, ?g2 x) i) \<in> A \<rightarrow>\<^sub>M M' i" if "i \<in> K \<inter> J" "i \<notin> I" for i
    using that measurable_compose[OF assms(5) measurable_component_singleton[OF that(1)]]
    by (simp add:merge_def)

  have a:"(\<lambda>x. merge I J (?g1 x, ?g2 x) i) \<in> A \<rightarrow>\<^sub>M M' i" if "i \<in> K" for i
    using assms(3) a1 a2 that by auto

  have "(\<lambda>x. h(merge I J (f x))) = (\<lambda>x. h(merge I J (?f1 x, ?f2 x)))" by simp
  also have "\<dots> = (\<lambda>x. h(\<lambda>i \<in> K. merge I J (?f1 x, ?f2 x) i))"
    using depends_onD[OF assms(1)] by simp
  also have "\<dots> = (\<lambda>x. h(\<lambda>i \<in> K. merge I J (?g1 x, ?g2 x) i))"
    by (intro ext arg_cong[where f="h"]) (auto simp:comp_def restrict_def merge_def case_prod_beta)
  also have "\<dots> \<in> A \<rightarrow>\<^sub>M N"
    by (intro measurable_compose[OF _ assms(2)] measurable_restrict a)
  finally show ?thesis by simp
qed

lemma measurable_compose_merge_2:
  assumes "depends_on h K" "h \<in> PiM K M' \<rightarrow>\<^sub>M N" "K \<subseteq> I \<union> J"
  assumes "(\<lambda>x. restrict (f x) (K \<inter> I)) \<in> A \<rightarrow>\<^sub>M PiM (K \<inter> I) M'"
  assumes "(\<lambda>x. restrict (g x) (K \<inter> J)) \<in> A \<rightarrow>\<^sub>M PiM (K \<inter> J) M'"
  shows "(\<lambda>x. h(merge I J (f x, g x))) \<in> A \<rightarrow>\<^sub>M N"
  using assms by (intro measurable_compose_merge_1[OF assms(1-3)]) simp_all

lemma neg_assoc_combine:
  fixes I I1 I2 :: "'i set"
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> ('b::linorder_topology)"
  assumes "finite I" "I1 \<union> I2 = I" "I1 \<inter> I2 = {}"
  assumes "indep_var (PiM I1 (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I1. X i \<omega>) (PiM I2 (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I2. X i \<omega>)"
  assumes "neg_assoc X I1"
  assumes "neg_assoc X I2"
  shows "neg_assoc X I"
proof -
  define X' where "X' i = (if i \<in> I then X i else (\<lambda>_. undefined))" for i

  have X_measurable: "random_variable borel (X i)" if "i \<in> I" for i
    using that assms(2) neg_assoc_imp_measurable[OF assms(5)]
      neg_assoc_imp_measurable[OF assms(6)] by auto

  have rv[measurable]: "random_variable borel (X' i)" for i
    unfolding X'_def using X_measurable by auto

  have na_I1: "neg_assoc X' I1" using neg_assoc_cong
    unfolding X'_def using assms(1,2) neg_assoc_imp_measurable[OF assms(5)]
    by (intro neg_assoc_cong[OF _ _ assms(5)] AE_I2) auto

  have na_I2: "neg_assoc X' I2" using neg_assoc_cong
    unfolding X'_def using assms(1,2) neg_assoc_imp_measurable[OF assms(6)]
    by (intro neg_assoc_cong[OF _ _ assms(6)] AE_I2) auto

  have iv:"indep_var(PiM I1 (\<lambda>_. borel))(\<lambda>\<omega>. \<lambda>i\<in>I1. X' i \<omega>)(PiM I2 (\<lambda>_. borel))(\<lambda>\<omega>. \<lambda>i\<in>I2. X' i \<omega>)"
    using assms(2,4) unfolding indep_var_def X'_def by (auto simp add:restrict_def cong:if_cong)

  let ?N = "Pi\<^sub>M I1 (\<lambda>_. borel) \<Otimes>\<^sub>M Pi\<^sub>M I2 (\<lambda>_. borel)"
  let ?A = "distr M (Pi\<^sub>M I1 (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I1. X' i \<omega>)"
  let ?B = "distr M (Pi\<^sub>M I2 (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I2. X' i \<omega>)"
  let ?H = "distr M ?N (\<lambda>\<omega>. (\<lambda>i\<in>I1. X' i \<omega>, \<lambda>i\<in>I2. X' i \<omega>))"

  have indep: "?H = (?A \<Otimes>\<^sub>M ?B)"
    and rvs: "random_variable (Pi\<^sub>M I1 (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I1. X' i \<omega>)"
             "random_variable (Pi\<^sub>M I2 (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I2. X' i \<omega>)"
    using iffD1[OF indep_var_distribution_eq iv] by auto

  interpret pa: prob_space ?A by (intro prob_space_distr rvs)
  interpret pb: prob_space ?B by (intro prob_space_distr rvs)
  interpret pair_sigma_finite ?A ?B
    using pa.sigma_finite_measure pb.sigma_finite_measure by (intro pair_sigma_finite.intro)

  interpret pab: prob_space "(?A \<Otimes>\<^sub>M ?B)"
    by (intro prob_space_pair pa.prob_space_axioms pb.prob_space_axioms)

  have pa_na: "pa.neg_assoc (\<lambda>x y. y x) I1"
    using assms(2) iffD1[OF neg_assoc_iff_distr na_I1] by fastforce

  have pb_na: "pb.neg_assoc (\<lambda>x y. y x) I2"
    using assms(2) iffD1[OF neg_assoc_iff_distr na_I2] by fastforce

  have na_X': "neg_assoc X' I"
  proof (rule neg_assocI2, goal_cases)
    case (1 i) thus ?case by measurable
  next
    case (2 f g K)

    note bounded_intros =
      bounded_range_imp[OF 2(6)] bounded_range_imp[OF 2(7)] pa.integrable_bounded
      pb.integrable_bounded pab.integrable_bounded bounded_intros pb.finite_measure_axioms

    have [measurable]:
      "restrict x I \<in> space (Pi\<^sub>M I (\<lambda>_. borel))" for x :: "('i \<Rightarrow> 'b)" and I by (simp add:space_PiM)

    have a: "K \<subseteq> I1 \<union> I2" using 2 assms(2) by auto
    have b: "I-K \<subseteq> I1 \<union> I2" using assms(2) by auto

    note merge_1 = measurable_compose_merge_2[OF 2(2,8) a] measurable_compose_merge_2[OF 2(3,9) b]
    note merge_2 = measurable_compose_merge_1[OF 2(2,8) a] measurable_compose_merge_1[OF 2(3,9) b]

    have merge_mono:
      "merge I1 I2 (w, y) \<le> merge I1 I2 (x, z)" if "w \<le> x" "y \<le> z" for w x y z :: "'i \<Rightarrow> 'b"
      using le_funD[OF that(1)] le_funD[OF that(2)] unfolding merge_def by (intro le_funI) auto

    have split_h: "h \<circ> flip X' = (\<lambda>\<omega>. h (merge I1 I2 (\<lambda>i\<in>I1. X' i \<omega>, \<lambda>i\<in>I2. X' i \<omega>)))"
      if "depends_on h I" for h :: "_ \<Rightarrow> real"
      using assms(2) unfolding comp_def
      by (intro ext depends_onD2[OF that]) (auto simp:restrict_def merge_def)

    have "depends_on f I" "depends_on g I"
      using 2(1) by (auto intro:depends_on_mono[OF _ 2(2)] depends_on_mono[OF _ 2(3)])
    note split = split_h[OF this(1)] split_h[OF this(2)]

    have step_1: "(\<integral>y. f (merge I1 I2 (x, y)) * g (merge I1 I2 (x, y)) \<partial>?B) \<le>
      (\<integral>y. f (merge I1 I2 (x, y))\<partial> ?B) * (\<integral>y. g (merge I1 I2 (x, y)) \<partial>?B)" (is "?L1 \<le> ?R1")
       for x
    proof -
      have step1_1: "monotone (\<le>) (\<le>\<ge>\<^bsub>Fwd\<^esub>) (\<lambda>a. f (merge I1 I2 (x, a)))"
        unfolding dir_le by (intro monoI monoD[OF 2(4)] merge_mono) simp
      have step1_2: "monotone (\<le>) (\<le>\<ge>\<^bsub>Fwd\<^esub>) (\<lambda>a. g (merge I1 I2 (x, a)))"
        unfolding dir_le by (intro monoI monoD[OF 2(5)] merge_mono) simp
      have step1_3: "depends_on (\<lambda>a. f (merge I1 I2 (x, a))) (K \<inter> I2)"
        by (subst depends_onD[OF 2(2)])
          (auto intro:depends_onI simp:merge_def restrict_def cong:if_cong)
      have step1_4: "depends_on (\<lambda>a. g (merge I1 I2 (x, a))) (I2 - K \<inter> I2)"
        by (subst depends_onD[OF 2(3)])
          (auto intro:depends_onI simp:merge_def restrict_def cong:if_cong)
      show ?thesis
        by (intro pb.neg_assoc_imp_mult_mono_bounded(2)[OF pb_na, where \<eta>="Fwd" and J="K \<inter> I2"]
            bounded_intros merge_1 step1_1 step1_2 step1_3 step1_4) measurable
    qed

    have step2_1: "monotone (\<le>) (\<le>\<ge>\<^bsub>Fwd\<^esub>) (\<lambda>a. pb.expectation (\<lambda>y. f (merge I1 I2 (a,y))))"
      unfolding dir_le
      by (intro monoI integral_mono bounded_intros merge_1 monoD[OF 2(4)] merge_mono) measurable

    have step2_2: "monotone (\<le>) (\<le>\<ge>\<^bsub>Fwd\<^esub>) (\<lambda>a. pb.expectation (\<lambda>y. g (merge I1 I2 (a,y))))"
      unfolding dir_le
      by (intro monoI integral_mono bounded_intros merge_1 monoD[OF 2(5)] merge_mono) measurable

    have step2_3: "depends_on (\<lambda>a. pb.expectation (\<lambda>y. f (merge I1 I2 (a, y)))) (K \<inter> I1)"
      by (subst depends_onD[OF 2(2)])
        (auto intro:depends_onI simp:merge_def restrict_def cong:if_cong)

    have step2_4: "depends_on (\<lambda>a. pb.expectation (\<lambda>y. g (merge I1 I2 (a, y)))) (I1-K\<inter>I1)"
      by (subst depends_onD[OF 2(3)])
        (auto intro:depends_onI simp:merge_def restrict_def cong:if_cong)

    have "(\<integral>\<omega>. (f\<circ>flip X') \<omega> * (g\<circ>flip X') \<omega> \<partial>M) = (\<integral>\<omega>. f (merge I1 I2 \<omega>) * g(merge I1 I2 \<omega>) \<partial>?H)"
      unfolding split by (intro integral_distr[symmetric] merge_2 borel_measurable_times) measurable
    also have "\<dots> = (\<integral>\<omega>. f(merge I1 I2 \<omega>) * g(merge I1 I2 \<omega>) \<partial> (?A \<Otimes>\<^sub>M ?B))"
      unfolding indep by simp
    also have "\<dots> = (\<integral>x. (\<integral>y. f(merge I1 I2 (x,y)) * g(merge I1 I2 (x,y)) \<partial>?B) \<partial>?A)"
      by (intro integral_fst'[symmetric] bounded_intros merge_2 borel_measurable_times)
        measurable
    also have "\<dots> \<le> (\<integral>x. (\<integral>y. f(merge I1 I2 (x,y)) \<partial>?B) * (\<integral>y. g(merge I1 I2 (x,y)) \<partial>?B) \<partial>?A)"
      by (intro integral_mono_AE bounded_intros step_1 AE_I2 pb.borel_measurable_lebesgue_integral
          borel_measurable_times iffD2[OF measurable_split_conv] merge_2) measurable
    also have "\<dots> \<le>(\<integral>x.(\<integral>y. f(merge I1 I2 (x,y))\<partial>?B)\<partial>?A)*(\<integral>x.(\<integral>y. g(merge I1 I2(x,y))\<partial>?B)\<partial>?A)"
      by (intro pa.neg_assoc_imp_mult_mono_bounded[OF pa_na, where \<eta>="Fwd" and J="K \<inter> I1"]
          bounded_intros pb.borel_measurable_lebesgue_integral iffD2[OF measurable_split_conv]
          merge_2 step2_1 step2_2 step2_3 step2_4) measurable
    also have "\<dots> = (\<integral>\<omega>. f(merge I1 I2 \<omega>) \<partial>(?A \<Otimes>\<^sub>M ?B)) * (\<integral>\<omega>. g(merge I1 I2 \<omega>) \<partial>(?A \<Otimes>\<^sub>M ?B))"
      by (intro arg_cong2[where f="(*)"] integral_fst' merge_2 bounded_intros) measurable
    also have "\<dots> = (\<integral>\<omega>. f(merge I1 I2 \<omega>) \<partial>?H) * (\<integral>\<omega>. g(merge I1 I2 \<omega>) \<partial>?H)"
      unfolding indep by simp
    also have "\<dots> = (\<integral>\<omega>. (f\<circ>flip X') \<omega> \<partial>M) * (\<integral>\<omega>. (g\<circ>flip X') \<omega> \<partial>M)"
      unfolding split by (intro arg_cong2[where f="(*)"] integral_distr merge_2) measurable
    finally show ?case by (simp add:comp_def)
  qed
  show ?thesis by (intro neg_assoc_cong[OF assms(1) X_measurable na_X']) (simp_all add:X'_def)
qed

text \<open>Property P7~\cite{joagdev1983}\<close>
lemma neg_assoc_union:
  fixes I :: "'i set"
  fixes p :: "'j \<Rightarrow> 'i set"
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> ('b::linorder_topology)"
  assumes "finite I" "\<Union>(p ` J) = I"
  assumes "indep_vars (\<lambda>j. PiM (p j) (\<lambda>_. borel)) (\<lambda>j \<omega>. \<lambda>i \<in> p j. X i \<omega>) J"
  assumes "\<And>j. j \<in> J \<Longrightarrow> neg_assoc X (p j)"
  assumes "disjoint_family_on p J"
  shows "neg_assoc X I"
proof -
  let ?B = "(\<lambda>_. borel)"
  define T where "T = {j \<in> J. p j \<noteq> {}}"

  define g where "g i = (THE j. j \<in> J \<and> i \<in> p j)" for i
  have g: "g i = j" if "i \<in> p j" "j \<in> J" for i j unfolding g_def
  proof (rule the1_equality)
    show "\<exists>!j. j \<in> J \<and> i \<in> p j"
      using assms(5) that unfolding bex1_def disjoint_family_on_def by auto
    show "j \<in> J \<and> i \<in> p j" using that by auto
  qed

  have ran_T: "T \<subseteq> J" unfolding T_def by simp
  hence "disjoint_family_on p T" using assms(5) disjoint_family_on_mono by metis
  moreover have "finite (\<Union>(p ` T))" using ran_T assms(1,2)
    by (meson Union_mono finite_subset image_mono)
  moreover have "\<And>i. i \<in> T \<Longrightarrow> p i \<noteq> {}" unfolding T_def by auto
  ultimately have fin_T: "finite T" using infinite_disjoint_family_imp_infinite_UNION by auto

  have "neg_assoc X (\<Union>(p ` T))"
    using fin_T ran_T
  proof (induction T rule:finite_induct)
    case empty thus ?case using neg_assoc_empty by simp
  next
    case (insert x F)

    note r = indep_var_compose[OF indep_var_restrict[OF assms(3), where A="F" and B="{x}"] _]

    have a: "(\<lambda>\<omega>. \<lambda>i\<in>\<Union>(p`F). X i \<omega>) = (\<lambda>\<omega>. \<lambda>i\<in>\<Union>(p`F). \<omega> (g i) i) \<circ> (\<lambda>\<omega>. \<lambda>i\<in>F. \<lambda>i\<in>p i. X i \<omega>)"
      using insert(4) g by (intro restrict_ext ext) auto
    have b: "(\<lambda>\<omega>. \<lambda>i\<in>p x. X i \<omega>) = (\<lambda>\<omega> i. \<omega> x i) \<circ> (\<lambda>\<omega>. \<lambda>i\<in>{x}. \<lambda>i\<in>p i. X i \<omega>)"
      by (simp add:comp_def restrict_def)

    have c:"(\<lambda>x. x (g i) i) \<in> borel_measurable (Pi\<^sub>M F (\<lambda>j. Pi\<^sub>M (p j) ?B))" if "i \<in> (\<Union>(p`F))" for i
    proof -
      have h: "i \<in> p (g i)" and q: "g i \<in> F" using g that insert(4) by auto
      thus ?thesis
        by (intro measurable_compose[OF measurable_component_singleton[OF q]]) measurable
    qed

    have "finite (\<Union> (p ` insert x F))" using assms(1,2) insert(4)
      by (meson Sup_subset_mono image_mono infinite_super)
    moreover have "\<Union> (p ` F) \<union> p x = \<Union> (p ` insert x F)" by auto
    moreover have "\<Union> (p ` F) \<inter> p x = {}"
      using assms(5) insert(2,4) unfolding disjoint_family_on_def by fast
    moreover have
      "indep_var (PiM (\<Union>(p`F)) ?B) (\<lambda>\<omega>. \<lambda>i\<in>\<Union>(p`F). X i \<omega>) (PiM (p x) ?B) (\<lambda>\<omega>. \<lambda>i\<in>p x. X i \<omega>)"
      unfolding a b using insert(1,2,4) by (intro r measurable_restrict c) simp_all
    moreover have "neg_assoc X (\<Union> (p ` F))" using insert(4) by (intro insert(3)) auto
    moreover have "neg_assoc X (p x)" using insert(4) by (intro assms(4)) auto
    ultimately show ?case by (rule neg_assoc_combine)
  qed
  moreover have "(\<Union>(p ` T)) = I" using assms(2) unfolding T_def by auto
  ultimately show ?thesis by auto
qed

text \<open>Property P5~\cite{joagdev1983}\<close>
lemma indep_imp_neg_assoc:
  assumes "finite I"
  assumes "indep_vars (\<lambda>_. borel) X I"
  shows "neg_assoc X I"
proof -
  have a:"neg_assoc X {i}" if "i \<in> I" for i
    using that assms(2) unfolding indep_vars_def
    by (intro neg_assoc_singleton) auto
  have b: "(\<Union>j\<in>I. {j}) = I" by auto
  have c: "indep_vars (\<lambda>j. Pi\<^sub>M {j} (\<lambda>_. borel)) (\<lambda>j \<omega>. \<lambda>i\<in>{j}. X j \<omega>) I"
    by (intro indep_vars_compose2[OF assms(2)]) measurable
  have d: "indep_vars (\<lambda>j. Pi\<^sub>M {j} (\<lambda>_. borel)) (\<lambda>j \<omega>. \<lambda>i\<in>{j}. X i \<omega>) I"
    by (intro iffD2[OF indep_vars_cong c] restrict_ext ext) auto
  show ?thesis by (intro neg_assoc_union[OF assms(1) b d a]) (auto simp:disjoint_family_on_def)
qed

end

lemma neg_assoc_map_pmf:
  shows "measure_pmf.neg_assoc (map_pmf f p) X I = measure_pmf.neg_assoc p (\<lambda>i \<omega>. X i (f \<omega>)) I"
    (is "?L \<longleftrightarrow> ?R")
proof -
  let ?d1 = "distr (measure_pmf (map_pmf f p)) (Pi\<^sub>M I (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I. X i \<omega>)"
  let ?d2 = "distr (measure_pmf p) (Pi\<^sub>M I (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>i\<in>I. X i (f \<omega>))"

  have "emeasure ?d1 A = emeasure ?d2 A" if "A \<in> sets (Pi\<^sub>M I (\<lambda>_. borel))" for A
  proof -
    have "emeasure ?d1 A = emeasure (measure_pmf p) {x. (\<lambda>i\<in>I. X i (f x)) \<in> A}"
      using that by (subst emeasure_distr) (simp_all add:vimage_def space_PiM)
    also have "\<dots> = emeasure ?d2 A"
      using that by (subst emeasure_distr) (simp_all add:space_PiM vimage_def)
    finally show ?thesis by simp
  qed

  hence a:"?d1 = ?d2" by (intro measure_eqI) auto

  have "?L \<longleftrightarrow> prob_space.neg_assoc ?d1 (\<lambda>x y. y x) I"
    by (subst measure_pmf.neg_assoc_iff_distr) auto
  also have "\<dots> \<longleftrightarrow> prob_space.neg_assoc ?d2 (\<lambda>x y. y x) I"
    unfolding a by simp
  also have "\<dots> \<longleftrightarrow> ?R"
    by (subst measure_pmf.neg_assoc_iff_distr) auto
  finally show ?thesis by simp
qed

end