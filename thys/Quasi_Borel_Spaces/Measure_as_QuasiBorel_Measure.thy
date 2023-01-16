(*  Title:   Measure_as_QuasiBorel_Measure.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open> Measure as QBS Measure\<close>
theory Measure_as_QuasiBorel_Measure
  imports "Pair_QuasiBorel_Measure"

begin

lemma distr_id':
  assumes "sets N = sets M"
          "f \<in> N \<rightarrow>\<^sub>M N"
      and "\<And>x. x \<in> space N \<Longrightarrow> f x = x"
    shows "distr N M f = N"
proof(rule measure_eqI)
  fix A
  assume 0:"A \<in> sets (distr N M f)"
  then have 1:"A \<subseteq> space N"
    by (auto simp: assms(1) sets.sets_into_space)

  have 2:"A \<in> sets M"
    using 0 by simp
  have 3:"f \<in> N \<rightarrow>\<^sub>M M"
    using assms(2) by(simp add: measurable_cong_sets[OF _ assms(1)])
  have "f -` A \<inter> space N = A"
  proof -
    have "f -` A = A \<union> {x. x \<notin> space N \<and> f x \<in> A}"
    proof(standard;standard)
      fix x
      assume h:"x \<in> f -` A"
      consider "x \<in> A" | "x \<notin> A"
        by auto
      thus "x \<in> A \<union> {x. x \<notin> space N \<and> f x \<in> A}"
      proof cases
        case 1
        then show ?thesis
          by simp
      next
        case 2
        have "x \<notin> space N"
        proof(rule ccontr)
          assume "\<not> x \<notin> space N"
          then have "x \<in> space N"
            by simp
          hence "f x = x"
            by(simp add: assms(3))
          hence "f x \<notin> A"
            by(simp add: 2)
          thus False
            using h by simp
        qed
        thus ?thesis
          using h by simp
      qed
    next
      fix x
      show "x \<in> A \<union> {x. x \<notin> space N \<and> f x \<in> A} \<Longrightarrow> x \<in> f -` A"
        using 1 assms by auto
    qed
    thus ?thesis
      using "1" by blast
  qed
  thus "emeasure (distr N M f) A = emeasure N A"
    by(simp add: emeasure_distr[OF 3 2])
qed (simp add: assms(1))

text \<open> Every probability measure on a standard Borel space can be represented as a measure on
       a quasi-Borel space~\<^cite>\<open>"Heunen_2017"\<close>, Proposition 23.\<close>
locale standard_borel_prob_space = standard_borel P + p:prob_space P
  for P :: "'a measure"
begin

sublocale qbs_prob "measure_to_qbs P" g "distr P real_borel f"
  by(auto intro!: qbs_probI p.prob_space_distr)

lift_definition as_qbs_measure :: "'a qbs_prob_space" is
"(measure_to_qbs P, g, distr P real_borel f)"
  by simp

lemma as_qbs_measure_retract:
  assumes [measurable]:"a \<in> P \<rightarrow>\<^sub>M real_borel"
      and [measurable]:"b \<in> real_borel \<rightarrow>\<^sub>M P"
      and [simp]:"\<And>x. x \<in> space P \<Longrightarrow> (b \<circ> a) x = x"
    shows "qbs_prob (measure_to_qbs P) b (distr P real_borel a)"
          "as_qbs_measure = qbs_prob_space (measure_to_qbs P, b, distr P real_borel a)"
proof -
  interpret pqp: pair_qbs_prob "measure_to_qbs P" g "distr P real_borel f" "measure_to_qbs P" b "distr P real_borel a"
    by(auto intro!: qbs_probI p.prob_space_distr simp: pair_qbs_prob_def)
  show "qbs_prob (measure_to_qbs P) b (distr P real_borel a)"
       "as_qbs_measure = qbs_prob_space (measure_to_qbs P, b, distr P real_borel a)"
    by(auto intro!: pqp.qbs_prob_space_eq
          simp: distr_distr distr_id'[OF standard_borel_lr_sets_ident[symmetric]] distr_id'[OF standard_borel_lr_sets_ident[symmetric] _ assms(3)] pqp.qp2.qbs_prob_axioms as_qbs_measure.abs_eq)
qed

lemma measure_as_qbs_measure_qbs:
 "qbs_prob_space_qbs as_qbs_measure = measure_to_qbs P"
  by transfer auto

lemma measure_as_qbs_measure_image:
 "as_qbs_measure \<in> monadP_qbs_Px (measure_to_qbs P)"
  by(auto simp: measure_as_qbs_measure_qbs monadP_qbs_Px_def)

lemma as_qbs_measure_as_measure[simp]:
 "distr (distr P real_borel f) (qbs_to_measure (measure_to_qbs P)) g = P"
  by(auto intro!: distr_id'[OF standard_borel_lr_sets_ident[symmetric]] simp : qbs_prob_t_measure_def distr_distr )


lemma measure_as_qbs_measure_recover:
 "qbs_prob_measure as_qbs_measure = P"
  by transfer (simp add: qbs_prob_t_measure_def)

end

lemma(in standard_borel) qbs_prob_measure_recover:
  assumes "q \<in> monadP_qbs_Px (measure_to_qbs M)"
  shows "standard_borel_prob_space.as_qbs_measure (qbs_prob_measure q) = q"
proof -
  obtain \<alpha> \<mu> where hq:
  "q = qbs_prob_space (measure_to_qbs M, \<alpha>, \<mu>)" "qbs_prob (measure_to_qbs M) \<alpha> \<mu>"
    using rep_monadP_qbs_Px[OF assms] by auto
  then interpret qp: qbs_prob "measure_to_qbs M" \<alpha> \<mu> by simp
  interpret sp: standard_borel_prob_space "distr \<mu> (qbs_to_measure (measure_to_qbs M)) \<alpha>"
    using qp.in_Mx
    by(auto intro!: prob_space.prob_space_distr
           simp: standard_borel_prob_space_def standard_borel_sets[OF sets_distr[of \<mu> "qbs_to_measure (measure_to_qbs M)" \<alpha>,simplified standard_borel_lr_sets_ident,symmetric]])
  interpret st: standard_borel "distr \<mu> M \<alpha>"
    by(auto intro!: standard_borel_sets)
  have [measurable]:"st.g \<in> real_borel \<rightarrow>\<^sub>M M"
    using measurable_distr_eq2 st.g_meas by blast
  show ?thesis
    by(auto intro!: pair_qbs_prob.qbs_prob_space_eq
          simp add: hq(1) sp.as_qbs_measure.abs_eq pair_qbs_prob_def qp.qbs_prob_axioms sp.qbs_prob_axioms)
     (simp_all add: measure_to_qbs_cong_sets[OF sets_distr[of \<mu> "qbs_to_measure (measure_to_qbs M)" \<alpha>,simplified standard_borel_lr_sets_ident]])
qed

lemma(in standard_borel_prob_space) ennintegral_as_qbs_ennintegral:
  assumes "k \<in> borel_measurable P"
  shows "(\<integral>\<^sup>+\<^sub>Q x. k x \<partial>as_qbs_measure) = (\<integral>\<^sup>+ x. k x \<partial>P)"
proof -
  have 1:"k \<in> measure_to_qbs P \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    using assms by auto
  thus ?thesis
    by(simp add: as_qbs_measure.abs_eq qbs_prob_ennintegral_def2[OF 1])
qed

lemma(in standard_borel_prob_space) integral_as_qbs_integral:
 "(\<integral>\<^sub>Q x. k x \<partial>as_qbs_measure) = (\<integral> x. k x \<partial>P)"
  by(simp add: as_qbs_measure.abs_eq qbs_prob_integral_def2)

lemma(in standard_borel) measure_with_args_morphism:
  assumes [measurable]:"\<mu> \<in> X \<rightarrow>\<^sub>M prob_algebra M"
  shows "standard_borel_prob_space.as_qbs_measure \<circ> \<mu> \<in> measure_to_qbs X \<rightarrow>\<^sub>Q monadP_qbs (measure_to_qbs M)"
proof(auto intro!: qbs_morphismI)
  fix \<alpha>
  assume h[measurable]:"\<alpha> \<in> real_borel \<rightarrow>\<^sub>M X"
  have "\<forall>r. (standard_borel_prob_space.as_qbs_measure \<circ> \<mu> \<circ> \<alpha>) r = qbs_prob_space (measure_to_qbs M, g, ((\<lambda>l. distr (\<mu> l) real_borel f) \<circ> \<alpha>) r)"
  proof auto
    fix r
    interpret sp: standard_borel_prob_space "\<mu> (\<alpha> r)"
      using measurable_space[OF assms measurable_space[OF h]]
      by(simp add: standard_borel_prob_space_def space_prob_algebra)
    have 1[measurable_cong]: "sets (\<mu> (\<alpha> r)) = sets M"
      using measurable_space[OF assms measurable_space[OF h]] by(simp add: space_prob_algebra)
    have 2:"f \<in> \<mu> (\<alpha> r) \<rightarrow>\<^sub>M real_borel" "g \<in> real_borel \<rightarrow>\<^sub>M \<mu> (\<alpha> r)" "\<And>x. x \<in> space (\<mu> (\<alpha> r)) \<Longrightarrow> (g \<circ> f) x = x"
      using measurable_space[OF assms measurable_space[OF h]]
      by(simp_all add: standard_borel_prob_space_def sets_eq_imp_space_eq[OF 1])
    show "standard_borel_prob_space.as_qbs_measure (\<mu> (\<alpha> r)) = qbs_prob_space (measure_to_qbs M, g, distr (\<mu> (\<alpha> r)) real_borel f)"
      by(simp add: sp.as_qbs_measure_retract[OF 2] measure_to_qbs_cong_sets[OF  subprob_measurableD(2)[OF measurable_prob_algebraD[OF assms] measurable_space[OF h]]])
  qed
  thus "standard_borel_prob_space.as_qbs_measure \<circ> \<mu> \<circ> \<alpha> \<in> monadP_qbs_MPx (measure_to_qbs M)"
    by(auto intro!: bexI[where x=g] bexI[where x="(\<lambda>l. distr (\<mu> l) real_borel f) \<circ> \<alpha>"] simp: monadP_qbs_MPx_def in_MPx_def)
qed

lemma(in standard_borel) measure_with_args_recover:
  assumes "\<mu> \<in> space X \<rightarrow> space (prob_algebra M)"
      and "x \<in> space X"
    shows "qbs_prob_measure (standard_borel_prob_space.as_qbs_measure (\<mu> x)) = \<mu> x"
    using standard_borel_sets[of "\<mu> x"] funcset_mem[OF assms]
    by(simp add: standard_borel_prob_space_def space_prob_algebra standard_borel_prob_space.measure_as_qbs_measure_recover)

subsection \<open>Example of Probability Measures\<close>
text \<open>Probability measures on $\mathbb{R}$ can be represented as probability measures on the quasi-Borel space $\mathbb{R}$.\<close>
subsubsection \<open> Normal Distribution \<close>
definition normal_distribution :: "real \<times> real \<Rightarrow> real measure" where
"normal_distribution \<mu>\<sigma> = (if 0 < (snd \<mu>\<sigma>) then density lborel (\<lambda>x. ennreal (normal_density (fst \<mu>\<sigma>) (snd \<mu>\<sigma>) x))
                                      else return lborel 0)"

lemma normal_distribution_measurable:
 "normal_distribution \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
proof(rule measurable_prob_algebra_generated[where \<Omega>=UNIV and G=borel])
  fix A :: "real set"
  assume h:"A \<in> sets borel"
  have "(\<lambda>x. emeasure (normal_distribution x) A) = (\<lambda>x. if 0 < (snd x) then emeasure (density lborel (\<lambda>r. ennreal (normal_density (fst x) (snd x) r))) A
                                                                                     else emeasure (return lborel 0) A)"
    by(auto simp add: normal_distribution_def)
  also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
  proof(rule measurable_If)
    have [simp]:"(\<lambda>x. indicat_real A (snd x)) \<in> borel_measurable ((borel \<Otimes>\<^sub>M borel) \<Otimes>\<^sub>M borel)"
    proof -
      have "(\<lambda>x. indicat_real A (snd x)) = indicat_real A \<circ> snd"
        by auto
      also have "... \<in> borel_measurable ((borel \<Otimes>\<^sub>M borel) \<Otimes>\<^sub>M borel)"
        by (meson borel_measurable_indicator h measurable_comp measurable_snd)
      finally show ?thesis .
    qed
    have "(\<lambda>x. emeasure (density lborel (\<lambda>r. ennreal (normal_density (fst x) (snd x) r))) A) = (\<lambda>x. set_nn_integral lborel A (\<lambda>r. ennreal (normal_density (fst x) (snd x) r)))"
      using h by(auto intro!: emeasure_density)
    also have "... = (\<lambda>x. \<integral>\<^sup>+r. ennreal (normal_density (fst x) (snd x) r * indicat_real A r)\<partial>lborel)"
      by(simp add: nn_integral_set_ennreal)
    also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
      apply(auto intro!: lborel.borel_measurable_nn_integral
                   simp: split_beta' measurable_cong_sets[OF sets_pair_measure_cong[OF refl sets_lborel]] )
      unfolding normal_density_def
      by(rule borel_measurable_times) simp_all
    finally show "(\<lambda>x. emeasure (density lborel (\<lambda>r. ennreal (normal_density (fst x) (snd x) r))) A) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)" .
  qed simp_all
  finally show "(\<lambda>x. emeasure (normal_distribution x) A) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)" .
qed (auto simp add: sets.sigma_sets_eq[of borel,simplified] sets.Int_stable prob_space_normal_density normal_distribution_def prob_space_return)

definition qbs_normal_distribution :: "real \<Rightarrow> real \<Rightarrow> real qbs_prob_space" where
"qbs_normal_distribution \<equiv> curry (standard_borel_prob_space.as_qbs_measure \<circ> normal_distribution)"

lemma qbs_normal_distribution_morphism:
 "qbs_normal_distribution \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<real>\<^sub>Q (monadP_qbs \<real>\<^sub>Q)"
  unfolding qbs_normal_distribution_def
  by(rule curry_preserves_morphisms[OF real.measure_with_args_morphism[OF normal_distribution_measurable,simplified r_preserves_product]])


context
  fixes \<mu> \<sigma> :: real
  assumes sigma:"\<sigma> > 0"
begin

interpretation n_dist:standard_borel_prob_space "normal_distribution (\<mu>,\<sigma>)"
  by(simp add: standard_borel_prob_space_def sigma prob_space_normal_density normal_distribution_def) 

lemma qbs_normal_distribution_def2:
 "qbs_normal_distribution \<mu> \<sigma> = n_dist.as_qbs_measure"
  by(simp add: qbs_normal_distribution_def)

lemma qbs_normal_distribution_integral:
 "(\<integral>\<^sub>Q x. f x \<partial> (qbs_normal_distribution \<mu> \<sigma>)) = (\<integral> x. f x \<partial> (density lborel (\<lambda>x. ennreal (normal_density \<mu> \<sigma> x))))"
  by(simp add: qbs_normal_distribution_def2 n_dist.integral_as_qbs_integral)
    (simp add: normal_distribution_def sigma)

lemma qbs_normal_distribution_expectation:
  assumes "f \<in> real_borel \<rightarrow>\<^sub>M real_borel"
    shows "(\<integral>\<^sub>Q x. f x \<partial> (qbs_normal_distribution \<mu> \<sigma>)) = (\<integral> x. normal_density \<mu> \<sigma> x * f x \<partial> lborel)"
  by(simp add: qbs_normal_distribution_integral assms integral_real_density integral_density)

end

subsubsection \<open> Uniform Distribution \<close>
definition interval_uniform_distribution :: "real \<Rightarrow> real \<Rightarrow> real measure" where
"interval_uniform_distribution a b \<equiv> (if a < b then uniform_measure lborel {a<..<b}
                                               else return lborel 0)"

lemma sets_interval_uniform_distribution[measurable_cong]:
 "sets (interval_uniform_distribution a b) = borel"
  by(simp add: interval_uniform_distribution_def)

lemma interval_uniform_distribution_meaurable:
 "(\<lambda>r. interval_uniform_distribution (fst r) (snd r)) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
proof(rule measurable_prob_algebra_generated[where \<Omega>=UNIV and G="range (\<lambda>(a, b). {a<..<b})"])
  show "sets real_borel = sigma_sets UNIV (range (\<lambda>(a, b). {a<..<b}))"
    by(simp add: borel_eq_box)
next
  show "Int_stable (range (\<lambda>(a, b). {a<..<b::real}))"
    by(fastforce intro!: Int_stableI simp: split_beta' image_iff)
next
  show "range (\<lambda>(a, b). {a<..<b}) \<subseteq> Pow UNIV"
    by simp
next
  fix a
  show "prob_space (interval_uniform_distribution (fst a) (snd a))"
    by(simp add: interval_uniform_distribution_def prob_space_return prob_space_uniform_measure)
next
  fix a
  show " sets (interval_uniform_distribution (fst a) (snd a)) = sets real_borel"
    by(simp add: interval_uniform_distribution_def)
next
  fix A
  assume "A \<in> range (\<lambda>(a, b). {a<..<b::real})"
  then obtain a b where ha:"A = {a<..<b}" by auto
  consider  "b \<le> a" | "a < b" by fastforce
  then show "(\<lambda>x. emeasure (interval_uniform_distribution (fst x) (snd x)) A) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M ennreal_borel"
             (is "?f \<in> ?meas")
  proof cases
    case 1
    then show ?thesis
      by(simp add: ha)
  next
    case h2:2
    have "?f = (\<lambda>x. if fst x < snd x then ennreal (min (snd x) b - max (fst x) a) / ennreal (snd x - fst x) else indicator A 0)"
    proof(standard; auto simp: interval_uniform_distribution_def ha)
      fix x y :: real
      assume hxy:"x < y"
      consider "b \<le> x" | "a \<le> x \<and> x < b" | "x < a \<and> a < y" | "y \<le> a"
        using h2 by fastforce
      thus "emeasure lborel ({max x a<..<min y b}) / ennreal (y - x) = ennreal (min y b - max x a) / ennreal (y - x)"
        by cases (use hxy ennreal_neg h2 in auto)
    qed
    also have "... \<in> ?meas"
      by simp
    finally show ?thesis .
  qed
qed

definition qbs_interval_uniform_distribution :: "real \<Rightarrow> real \<Rightarrow> real qbs_prob_space" where
"qbs_interval_uniform_distribution \<equiv> curry (standard_borel_prob_space.as_qbs_measure \<circ> (\<lambda>r. interval_uniform_distribution (fst r) (snd r)))"

lemma qbs_interval_uniform_distribution_morphism:
 "qbs_interval_uniform_distribution \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<real>\<^sub>Q (monadP_qbs \<real>\<^sub>Q)"
  unfolding qbs_interval_uniform_distribution_def
  using curry_preserves_morphisms[OF real.measure_with_args_morphism[OF interval_uniform_distribution_meaurable,simplified r_preserves_product]] .

context
  fixes a b :: real
  assumes a_less_than_b:"a < b"
begin

definition "ab_qbs_uniform_distribution \<equiv> qbs_interval_uniform_distribution a b"

interpretation ab_u_dist: standard_borel_prob_space "interval_uniform_distribution a b"
  by(auto intro!: prob_space_uniform_measure simp: interval_uniform_distribution_def standard_borel_prob_space_def prob_space_return)

lemma qbs_interval_uniform_distribution_def2:
 "ab_qbs_uniform_distribution = ab_u_dist.as_qbs_measure"
  by(simp add: qbs_interval_uniform_distribution_def ab_qbs_uniform_distribution_def)

lemma qbs_uniform_distribution_expectation:
  assumes "f \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "(\<integral>\<^sup>+\<^sub>Q x. f x \<partial>ab_qbs_uniform_distribution) = (\<integral>\<^sup>+x \<in> {a<..<b}. f x \<partial>lborel) / (b - a)"
        (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+x. f x \<partial>(interval_uniform_distribution a b))"
    using assms by(auto simp: qbs_interval_uniform_distribution_def2 intro!:ab_u_dist.ennintegral_as_qbs_ennintegral dest:ab_u_dist.qbs_morphism_dest[simplified measure_to_qbs_cong_sets[OF sets_interval_uniform_distribution]])
  also have "... = ?rhs"
    using assms
    by(auto simp: interval_uniform_distribution_def a_less_than_b intro!:nn_integral_uniform_measure[where M=lborel and S="{a<..<b}",simplified emeasure_lborel_Ioo[OF order.strict_implies_order[OF a_less_than_b]]])
  finally show ?thesis .
qed

end

subsubsection \<open> Bernoulli Distribution \<close>
definition qbs_bernoulli :: "real \<Rightarrow> bool qbs_prob_space" where
"qbs_bernoulli \<equiv> standard_borel_prob_space.as_qbs_measure \<circ> (\<lambda>x. measure_pmf (bernoulli_pmf x))"

lemma bernoulli_measurable:
 "(\<lambda>x. measure_pmf (bernoulli_pmf x)) \<in> real_borel \<rightarrow>\<^sub>M prob_algebra bool_borel"
proof(rule measurable_prob_algebra_generated[where \<Omega>=UNIV and G=UNIV],simp_all)
  fix A :: "bool set"
  have "A \<subseteq> {True,False}"
    by auto
  then consider "A = {}" | "A = {True}" | "A = {False}" | "A = {False,True}"
    by auto
  thus "(\<lambda>a. emeasure (measure_pmf (bernoulli_pmf a)) A) \<in> borel_measurable borel"
    by(cases,simp_all add: emeasure_measure_pmf_finite bernoulli_pmf.rep_eq UNIV_bool[symmetric])
qed (auto simp add: sets_borel_eq_count_space Int_stable_def measure_pmf.prob_space_axioms)

lemma qbs_bernoulli_morphism:
 "qbs_bernoulli \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q monadP_qbs \<bool>\<^sub>Q"
  using bool.measure_with_args_morphism[OF bernoulli_measurable]
  by (simp add: qbs_bernoulli_def)


lemma qbs_bernoulli_measure:
 "qbs_prob_measure (qbs_bernoulli p) = measure_pmf (bernoulli_pmf p)"
  using bool.measure_with_args_recover[of "\<lambda>x. measure_pmf (bernoulli_pmf x)" real_borel p] bernoulli_measurable
  by(simp add: measurable_def qbs_bernoulli_def)

context
  fixes p :: real
  assumes pgeq_0[simp]:"0 \<le> p" and pleq_1[simp]:"p \<le> 1"
begin

lemma qbs_bernoulli_expectation:
  "(\<integral>\<^sub>Q x. f x \<partial>qbs_bernoulli p) = f True * p + f False * (1 - p)"
  by(simp add: qbs_prob_integral_def2 qbs_bernoulli_measure)

end

end