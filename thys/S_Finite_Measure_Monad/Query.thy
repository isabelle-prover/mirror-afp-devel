(*  Title:   Query.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Query\<close>

theory Query
  imports "Monad_QuasiBorel"
begin

declare [[coercion qbs_l]]
abbreviation qbs_real :: "real quasi_borel"       ("\<real>\<^sub>Q") where "\<real>\<^sub>Q \<equiv> qbs_borel"
abbreviation qbs_ennreal :: "ennreal quasi_borel" ("\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0") where "\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<equiv> qbs_borel"
abbreviation qbs_nat :: "nat quasi_borel"         ("\<nat>\<^sub>Q") where "\<nat>\<^sub>Q \<equiv> qbs_count_space UNIV"
abbreviation qbs_bool :: "bool quasi_borel"       ("\<bool>\<^sub>Q") where "\<bool>\<^sub>Q \<equiv> count_space\<^sub>Q UNIV"


definition query :: "['a qbs_measure, 'a \<Rightarrow> ennreal] \<Rightarrow> 'a qbs_measure" where
"query \<equiv> (\<lambda>s f. normalize_qbs (density_qbs s f))"

lemma query_qbs_morphism[qbs]: "query \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q monadM_qbs X"
  by(simp add: query_def)

definition "condition \<equiv> (\<lambda>s P. query s (\<lambda>x. if P x then 1 else 0))"

lemma condition_qbs_morphism[qbs]: "condition \<in> monadM_qbs X \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q \<bool>\<^sub>Q) \<Rightarrow>\<^sub>Q monadM_qbs X"
  by(simp add: condition_def)

lemma condition_morphismP:
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> \<P>(y in qbs_l (s x). P x y) \<noteq> 0"
      and [qbs]: "s \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y" "P \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
    shows "(\<lambda>x. condition (s x) (P x)) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
proof(rule qbs_morphism_cong'[where f="\<lambda>x. normalize_qbs (density_qbs (s x) (indicator {y\<in>qbs_space Y. P x y}))"])
  fix x
  assume x[qbs]:"x \<in> qbs_space X"
  have "density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y}) = density_qbs (s x) (\<lambda>y. if P x y then 1 else 0)"
    by(auto intro!: density_qbs_cong[OF qbs_space_monadPM[OF qbs_morphism_space[OF assms(2) x]]] indicator_qbs_morphism'')
  thus "normalize_qbs (density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y})) = condition (s x) (P x)"
    unfolding condition_def query_def by simp
next
  show "(\<lambda>x. normalize_qbs (density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y}))) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  proof(rule normalize_qbs_morphismP[of "\<lambda>x. density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y})"])
    show "(\<lambda>x. density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y})) \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
      using qbs_morphism_monadPD[OF assms(2)] by simp
  next
    fix x
    assume x:"x \<in> qbs_space X"
    show "emeasure (qbs_l (density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y}))) (qbs_space Y) \<noteq> 0"
         "emeasure (qbs_l (density_qbs (s x) (indicator {y \<in> qbs_space Y. P x y}))) (qbs_space Y) \<noteq> \<infinity>"
      using assms(1)[OF x] qbs_l_monadP_le1[OF qbs_morphism_space[OF assms(2) x]]
      by(auto simp add: qbs_l_density_qbs_indicator[OF qbs_space_monadPM[OF qbs_morphism_space[OF assms(2) x]] qbs_morphism_space[OF assms(3) x]] measure_def space_qbs_l_in[OF qbs_space_monadPM[OF qbs_morphism_space[OF assms(2) x]]])
  qed
qed

lemma query_Bayes:
  assumes [qbs]: "s \<in> qbs_space (monadP_qbs X)" "qbs_pred X P" "qbs_pred X Q"
  shows "\<P>(x in condition s P. Q x) = \<P>(x in s. Q x \<bar> P x)" (is "?lhs = ?pq")
proof -
  have X: "qbs_space X \<noteq> {}"
    using assms(1) by(simp only: monadP_qbs_empty_iff[of X]) blast
  note s[qbs] = qbs_space_monadPM[OF assms(1)]
  have density_eq: "density_qbs s (\<lambda>x. if P x then 1 else 0) = density_qbs s (indicator {x\<in>qbs_space X. P x})"
    by(auto intro!: density_qbs_cong[of _ X] indicator_qbs_morphism'')
  consider "emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X) = 0" | "emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X) \<noteq> 0" by auto
  then show ?thesis
  proof cases
    case 1
    have 2:"normalize_qbs (density_qbs s (\<lambda>x. if P x then 1 else 0)) = qbs_null_measure X"
      by(rule normalize_qbs0) (auto simp: 1)
    have "\<P>(\<omega> in qbs_l s. P \<omega>) = measure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)"
      by(simp add: space_qbs_l_in[OF s] measure_def density_eq qbs_l_density_qbs_indicator[OF s])
    also have "... = 0"
      by(simp add: measure_def 1)
    finally show ?thesis
      by(auto simp: condition_def query_def cond_prob_def 2 1 qbs_null_measure_null_measure[OF X])
  next
    case 1[simp]:2
    from rep_qbs_space_monadP[OF assms(1)]
    obtain \<alpha> \<mu> where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_prob X \<alpha> \<mu>" by auto
    then interpret qp: qbs_prob X \<alpha> \<mu> by simp
    have [measurable]:"Measurable.pred (qbs_to_measure X) P" "Measurable.pred (qbs_to_measure X) Q"
      using assms(2,3) by(simp_all add: lr_adjunction_correspondence)
    have 2[simp]: "emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X) \<noteq> \<top>"
      by(simp add: hs(1) qp.density_qbs qbs_s_finite.qbs_l[OF qp.density_qbs_s_finite] emeasure_distr emeasure_distr[where N="qbs_to_measure X",OF _ sets.top,simplified space_L] emeasure_density,rule order.strict_implies_not_eq[OF order.strict_trans1[OF qp.nn_integral_le_const[of 1] ennreal_one_less_top]]) auto
    have 3: "measure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X) > 0"
      using 2 emeasure_eq_ennreal_measure zero_less_measure_iff by fastforce
    have "query s (\<lambda>x. if P x then 1 else 0) = density_qbs (density_qbs s (\<lambda>x. if P x then 1 else 0)) (\<lambda>x. 1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X))"
      unfolding query_def by(rule normalize_qbs) auto
    also have "... = density_qbs s (\<lambda>x. (if P x then 1 else 0) * (1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)))"
      by(simp add: density_qbs_density_qbs_eq[OF qbs_space_monadPM[OF assms(1)]])
    finally have query:"query s (\<lambda>x. if P x then 1 else 0) = ..." .
    have "?lhs = measure (density (qbs_l s) (\<lambda>x. (if P x then 1 else 0) * (1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)))) {x \<in> space (qbs_l s). Q x}"
      by(simp add: condition_def query qbs_l_density_qbs[OF qbs_space_monadPM[OF assms(1)]])
    also have "... = measure (density \<mu> (\<lambda>x. (if P (\<alpha> x) then 1 else 0) * (1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)))) {y. \<alpha> y \<in> space (qbs_to_measure X) \<and> Q (\<alpha> y)}"
      by(simp add: hs(1) qp.qbs_l  density_distr measure_def emeasure_distr)
    also have "... = measure (density \<mu> (\<lambda>x. indicator {r. P (\<alpha> r)} x * (1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)))) {y. Q (\<alpha> y)}"
    proof -
      have [simp]:"(if P (\<alpha> r) then 1 else 0) = indicator {r. P (\<alpha> r)} r " for r
        by auto
      thus ?thesis by(simp add: space_L)
    qed
    also have "... = enn2real (1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)) * measure \<mu> {r. P (\<alpha> r) \<and> Q (\<alpha> r)}"
    proof -
      have n_inf: "1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X) \<noteq> \<infinity>"
        using 1 by(auto simp: ennreal_divide_eq_top_iff)
      show ?thesis
        by(simp add: measure_density_times[OF _ _ n_inf] Collect_conj_eq)
    qed
    also have "... = (1 / measure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)) * qp.prob {r. P (\<alpha> r) \<and> Q (\<alpha> r)}"
    proof -
      have "1 / emeasure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X) = ennreal (1 / measure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X))"
        by(auto simp add: emeasure_eq_ennreal_measure[OF 2] ennreal_1[symmetric] simp del: ennreal_1 intro!: divide_ennreal) (simp_all add: 3)
      thus ?thesis by simp
    qed  also have "... = ?pq"
    proof -
      have qp:"\<P>(x in s. Q x \<and> P x) = qp.prob {r. P (\<alpha> r) \<and> Q (\<alpha> r)}"
        by(auto simp: hs(1) qp.qbs_l measure_def emeasure_distr, simp add: space_L) meson
      note sets = sets_qbs_l[OF qbs_space_monadPM[OF assms(1)],measurable_cong]
      have [simp]: "density (qbs_l s) (\<lambda>x. if P x then 1 else 0) = density (qbs_l s) (indicator {x\<in>space (qbs_to_measure X). P x})"
        by(auto intro!: density_cong) (auto simp: indicator_def space_L sets_eq_imp_space_eq[OF sets])
      have p: "\<P>(x in s. P x) = measure (qbs_l (density_qbs s (\<lambda>x. if P x then 1 else 0))) (qbs_space X)"
        by(auto simp: qbs_l_density_qbs[OF qbs_space_monadPM[OF assms(1),qbs]]) (auto simp: measure_restricted[of "{x \<in> space (qbs_to_measure X). P x}" "qbs_l s",simplified sets,OF _ sets.top,simplified,simplified space_L] space_L sets_eq_imp_space_eq[OF sets])
      thus ?thesis
        by(simp add: qp p cond_prob_def)
    qed
    finally show ?thesis .
  qed
qed

lemma qbs_pmf_cond_pmf:
  fixes p :: "'a :: countable pmf"
  assumes "set_pmf p \<inter> {x. P x} \<noteq> {}"
  shows "condition (qbs_pmf p) P = qbs_pmf (cond_pmf p {x. P x})"
proof(rule inj_onD[OF qbs_l_inj[of "count_space UNIV"]])
  note count_space_count_space_qbs_morphism[of P,qbs]
  show g1:"condition (qbs_pmf p) P \<in> qbs_space (monadM_qbs (count_space\<^sub>Q UNIV))" "qbs_pmf (cond_pmf p {x. P x}) \<in> qbs_space (monadM_qbs (count_space\<^sub>Q UNIV))"
    by auto
  show "qbs_l (condition (qbs_pmf p) P) = qbs_l (qbs_pmf (cond_pmf p {x. P x}))"
  proof(safe intro!: measure_eqI_countable)
    fix a
    have "condition (qbs_pmf p) P = normalize_qbs (density_qbs (qbs_pmf p) (\<lambda>x. if P x then 1 else 0))"
      by(auto simp: condition_def query_def)
    also have "... = density_qbs (density_qbs (qbs_pmf p) (\<lambda>x. if P x then 1 else 0)) (\<lambda>x. 1 / emeasure (qbs_l (density_qbs (qbs_pmf p) (\<lambda>x. if P x then 1 else 0))) (qbs_space (count_space\<^sub>Q UNIV)))"
    proof -
      have 1:"(\<integral>\<^sup>+ x. ennreal (pmf p x) * (if P x then 1 else 0) \<partial>count_space UNIV) = (\<integral>\<^sup>+ x\<in>{x. P x}. ennreal (pmf p x) \<partial>count_space UNIV)"
        by(auto intro!: nn_integral_cong)
      have "... > 0"
        using assms(1) by(force intro!: nn_integral_less[of "\<lambda>x. 0",simplified] simp: AE_count_space set_pmf_eq' indicator_def)
      hence 2:"(\<integral>\<^sup>+x\<in>{x. P x}. ennreal (pmf p x) \<partial>count_space UNIV) \<noteq> 0"
        by auto
      have 3:"(\<integral>\<^sup>+ x\<in>{x. P x}. ennreal (pmf p x) \<partial>count_space UNIV) \<noteq> \<top>"
      proof -
        have "(\<integral>\<^sup>+ x\<in>{x. P x}. ennreal (pmf p x) \<partial>count_space UNIV) \<le> (\<integral>\<^sup>+ x. ennreal (pmf p x) \<partial>count_space UNIV)"
          by(auto intro!: nn_integral_mono simp: indicator_def)
        also have "... = 1"
          by (simp add: nn_integral_pmf_eq_1)
        finally show ?thesis
          using ennreal_one_neq_top neq_top_trans by fastforce
      qed
      show ?thesis
        by(rule normalize_qbs) (auto simp: qbs_l_density_qbs[of _ "count_space UNIV"] emeasure_density nn_integral_measure_pmf 1 2 3)
    qed
    also have "... = density_qbs (qbs_pmf p) (\<lambda>x. (if P x then 1 else 0) * (1 / (\<integral>\<^sup>+ x. ennreal (pmf p x) * (if P x then 1 else 0) \<partial>count_space UNIV)))"
      by(simp add: density_qbs_density_qbs_eq[of _ "count_space UNIV"] qbs_l_density_qbs[of _ "count_space UNIV"] emeasure_density nn_integral_measure_pmf)
    also have "... = density_qbs (qbs_pmf p) (\<lambda>x. (if P x then 1 else 0) * (1 / (emeasure (measure_pmf p) (Collect P))))"
    proof -
      have [simp]: "(\<integral>\<^sup>+ x. ennreal (pmf p x) * (if P x then 1 else 0) \<partial>count_space UNIV) = emeasure (measure_pmf p) (Collect P)" (is "?l = ?r")
      proof -
        have "?l = (\<integral>\<^sup>+ x. ennreal (pmf p x) * (if P x then 1 else 0) \<partial>count_space {x. P x})"
          by(rule  nn_integral_count_space_eq) auto
        also have "... = ?r"
          by(auto simp: nn_integral_pmf[symmetric] intro!: nn_integral_cong)
        finally show ?thesis .
      qed
      show ?thesis by simp
    qed 
    finally show "emeasure (qbs_l (condition (qbs_pmf p) P)) {a} = emeasure (qbs_l (qbs_pmf (cond_pmf p {x. P x}))) {a}"
      by(simp add: ennreal_divide_times qbs_l_density_qbs[of _ "count_space UNIV"] emeasure_density cond_pmf.rep_eq[OF assms(1)])
  qed(auto simp: sets_qbs_l[OF g1(1)])
qed

subsubsection \<open>\texttt{twoUs}\<close>
text \<open> Example from Section~2 in @{cite Sato_2019}.\<close>
definition "Uniform \<equiv> (\<lambda>a b::real. uniform_qbs lborel_qbs {a<..<b})"

lemma Uniform_qbs[qbs]: "Uniform \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q"
  unfolding Uniform_def by (rule interval_uniform_qbs)

definition twoUs :: "(real \<times> real) qbs_measure" where
"twoUs \<equiv> do {
              let u1 = Uniform 0 1;
              let u2 = Uniform 0 1;
              let y = u1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s u2;
              condition y (\<lambda>(x,y). x < 0.5 \<or> y > 0.5)
             }"

lemma twoUs_qbs: "twoUs \<in> monadM_qbs (\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q)"
  by(simp add: twoUs_def)

interpretation rr: standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(simp add: borel_prod)

lemma qbs_l_Uniform[simp]: "a < b \<Longrightarrow> qbs_l (Uniform a b) = uniform_measure lborel {a<..<b}"
  by(simp add: standard_borel_ne.qbs_l_uniform_qbs[of borel lborel_qbs] Uniform_def)

lemma Uniform_qbsP:
  assumes [arith]: "a < b"
  shows "Uniform a b \<in> monadP_qbs \<real>\<^sub>Q"
  by(auto simp: monadP_qbs_def sub_qbs_space intro!: prob_space_uniform_measure)

interpretation UniformP_pair: pair_prob_space "uniform_measure lborel {0<..<1::real}" "uniform_measure lborel {0<..<1::real}"
  by(auto simp: pair_prob_space_def pair_sigma_finite_def intro!: prob_space_imp_sigma_finite prob_space_uniform_measure)

lemma qbs_l_Uniform_pair: "a < b \<Longrightarrow> qbs_l (Uniform a b \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform a b) = uniform_measure lborel {a<..<b} \<Otimes>\<^sub>M uniform_measure lborel {a<..<b}"
  by(auto intro!: qbs_l_qbs_pair_measure[of borel borel] standard_borel_ne.standard_borel simp: qbs_l_Uniform[symmetric] simp del: qbs_l_Uniform)

lemma Uniform_pair_qbs[qbs]:
  assumes "a < b"
  shows "Uniform a b \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform a b \<in> qbs_space (monadP_qbs (\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q))"
proof -
  note [qbs] = qbs_pair_measure_morphismP Uniform_qbsP[OF assms]
  show ?thesis
    by simp
qed

lemma twoUs_prob1: "\<P>(z in Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1. fst z < 0.5 \<or> snd z > 0.5) = 3 / 4"
proof -
  have [simp]:"{z \<in> space (uniform_measure lborel {0<..<1::real} \<Otimes>\<^sub>M uniform_measure lborel {0<..<1::real}). fst z * 2 < 1 \<or> 1 < snd z * 2} = UNIV \<times> {1/2<..} \<union> {..<1/2} \<times> UNIV"
    by(auto simp: space_pair_measure)
  have 1:"UniformP_pair.prob (UNIV \<times> {1 / 2<..}) = 1 / 2"
  proof -
    have [simp]:"{0<..<1} \<inter> {1 / 2<..} = {1/2<..<1::real}" by auto
    thus ?thesis
      by(auto simp: UniformP_pair.M1.measure_times)
  qed
  have 2:"UniformP_pair.prob ({..<1 / 2} \<times> UNIV - UNIV \<times> {1 / 2<..}) = 1 / 4"
  proof -
    have [simp]: "{..<1/2::real} \<times> UNIV - UNIV \<times> {1/2::real<..} = {..<1/2} \<times> {..1/2}" "{0<..<1} \<inter> {..<1/2} = {0<..<1/2::real}" "{0<..<1} \<inter> {..1/2::real} = {0<..1/2}"
      by auto
    show ?thesis
      by(auto simp: UniformP_pair.M1.measure_times)
  qed
  show ?thesis
    by(auto simp: qbs_l_Uniform_pair UniformP_pair.P.finite_measure_Union' 1 2)
qed

lemma twoUs_prob2:"\<P>(z in Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1. 1/2 < fst z \<and> (fst z < 1/2 \<or> snd z > 1/2)) = 1 / 4"
proof -
  have [simp]:"{z \<in> space (uniform_measure lborel {0<..<1::real} \<Otimes>\<^sub>M uniform_measure lborel {0<..<1::real}). 1 < fst z * 2 \<and> (fst z * 2 < 1 \<or> 1 < snd z * 2)} = {1/2<..} \<times> {1/2<..}"
    by(auto simp: space_pair_measure)
  have [simp]: "{0<..<1::real} \<inter> {1/2<..} = {1/2<..<1}" by auto
  show ?thesis
    by(auto simp: qbs_l_Uniform_pair UniformP_pair.M1.measure_times)
qed

lemma twoUs_qbs_prob: "twoUs \<in> qbs_space (monadP_qbs (\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q))" 
proof -
  have "\<P>(z in Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1. fst z < 0.5 \<or> snd z > 0.5) \<noteq> 0"
    unfolding twoUs_prob1 by simp
  note qbs_morphism_space[OF condition_morphismP[of qbs_borel "\<lambda>x. Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1" "\<lambda>x z. fst z < 0.5 \<or> snd z > 0.5" "\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q",OF this],simplified,qbs]
  note Uniform_pair_qbs[of 0 1,simplified,qbs]
  show ?thesis
    by(simp add: twoUs_def split_beta')
qed

lemma "\<P>((x,y) in twoUs. 1/2 < x) = 1 / 3"
proof -
  have "\<P>((x,y) in twoUs. 1/2 < x) = \<P>(z in twoUs. 1/2 < fst z)"
    by (simp add: split_beta')
  also have "... = \<P>(z in Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1. 1/2 < fst z \<bar> fst z < 0.5 \<or> snd z > 0.5)"
    by(simp add: twoUs_def split_beta',rule query_Bayes[OF Uniform_pair_qbs[of 0 1,simplified,qbs]]) auto
  also have "... = \<P>(z in Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1. 1/2 < fst z \<and> (fst z < 1/2 \<or> snd z > 1/2)) / \<P>(z in Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1. fst z < 0.5 \<or> snd z > 0.5)"
    by(simp add: cond_prob_def)
  also have "... = 1 / 3"
    by(simp only: twoUs_prob2 twoUs_prob1) simp
  finally show ?thesis .
qed

subsubsection \<open> Two Dice \<close>
text \<open> Example from Adrian~\cite[Sect.~2.3]{Adrian_PL}.\<close>
abbreviation "die \<equiv> qbs_pmf (pmf_of_set {Suc 0..6})"

lemma die_qbs[qbs]: "die \<in> monadM_qbs \<nat>\<^sub>Q"
  by simp

definition two_dice :: "nat qbs_measure" where
 "two_dice \<equiv> do {
                let die1 = die;
                let die2 = die;
                let twodice = die1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s die2;
                (x,y) \<leftarrow> condition twodice
                        (\<lambda>(x,y). x = 4 \<or> y = 4);
                return_qbs \<nat>\<^sub>Q (x + y)
              }"

lemma two_dice_qbs: "two_dice \<in> monadM_qbs \<nat>\<^sub>Q"
  by(simp add: two_dice_def)

lemma prob_die2: "\<P>(x in qbs_l (die \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s die). P x) = real (card ({x. P x} \<inter> ({1..6} \<times> {1..6}))) / 36" (is "?P = ?rhs")
proof -
  have "?P = measure_pmf.prob (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {x. P x}"
    by(auto simp: qbs_pair_pmf)
  also have "... = measure_pmf.prob (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) ({x. P x} \<inter> set_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})))"
    by(rule measure_Int_set_pmf[symmetric])
  also have "... = measure_pmf.prob (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) ({x. P x} \<inter> ({Suc 0..6} \<times> {Suc 0..6}))"
    by simp
  also have "... = (\<Sum>z\<in>{x. P x} \<inter> ({Suc 0..6} \<times> {Suc 0..6}). pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) z)"
    by(simp add: measure_measure_pmf_finite)
  also have "... = (\<Sum>z\<in>{x. P x} \<inter> ({Suc 0..6} \<times> {Suc 0..6}). 1 / 36)"
    by(rule Finite_Cartesian_Product.sum_cong_aux) (auto simp: pmf_pair)
  also have "... = ?rhs"
    by auto
  finally show ?thesis .
qed

lemma dice_prob1: "\<P>(z in qbs_l (die \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s die). fst z = 4 \<or> snd z = 4) = 11 / 36"
proof -
  have 1:"Restr {z. fst z = 4 \<or> snd z = 4} {Suc 0..6::nat} = {Suc 0..Suc (Suc (Suc (Suc (Suc (Suc 0)))))} \<times> {Suc (Suc (Suc (Suc 0)))} \<union> {Suc (Suc (Suc (Suc 0)))} \<times> {Suc 0..(Suc (Suc (Suc 0)))} \<union> {Suc (Suc (Suc (Suc 0)))} \<times> {Suc (Suc (Suc (Suc (Suc 0))))..Suc (Suc (Suc (Suc (Suc (Suc 0)))))}"
    by fastforce
  have "card ... = card ({Suc 0..Suc (Suc (Suc (Suc (Suc (Suc 0)))))} \<times> {Suc (Suc (Suc (Suc 0)))} \<union> {Suc (Suc (Suc (Suc 0)))} \<times> {Suc 0..(Suc (Suc (Suc 0)))}) + card ({Suc (Suc (Suc (Suc 0)))} \<times> {Suc (Suc (Suc (Suc (Suc 0))))..Suc (Suc (Suc (Suc (Suc (Suc 0)))))})"
    by(rule card_Un_disjnt) (auto simp: disjnt_def)
  also have "... = card ({Suc 0..Suc (Suc (Suc (Suc (Suc (Suc 0)))))} \<times> {Suc (Suc (Suc (Suc 0)))}) + card ({Suc (Suc (Suc (Suc 0)))} \<times> {Suc 0..(Suc (Suc (Suc 0)))}) + card ({Suc (Suc (Suc (Suc 0)))} \<times> {Suc (Suc (Suc (Suc (Suc 0))))..Suc (Suc (Suc (Suc (Suc (Suc 0)))))})"
  proof -
    have "card ({Suc 0..Suc (Suc (Suc (Suc (Suc (Suc 0)))))} \<times> {Suc (Suc (Suc (Suc 0)))} \<union> {Suc (Suc (Suc (Suc 0)))} \<times> {Suc 0..(Suc (Suc (Suc 0)))}) = card ({Suc 0..Suc (Suc (Suc (Suc (Suc (Suc 0)))))} \<times> {Suc (Suc (Suc (Suc 0)))}) + card ({Suc (Suc (Suc (Suc 0)))} \<times> {Suc 0..(Suc (Suc (Suc 0)))})"
      by(rule card_Un_disjnt) (auto simp: disjnt_def)
    thus ?thesis by simp
  qed
  also have "... = 11" by auto
  finally show ?thesis
    by(auto simp: prob_die2 1)
qed

lemma dice_program_prob:"\<P>(x in two_dice. P x) = 2 * (\<Sum>n\<in>{5,6,7,9,10}. of_bool (P n) / 11) + of_bool (P 8) / 11" (is "?P = ?rp")
proof -
  have 0: "(\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x}) = {5,6,7,8,9,10}"
  proof safe
    show " 5 \<in> (\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x})"
      by(auto intro!: bexI[where x="(1,4)"])
    show "6 \<in> (\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x})"
      by(auto intro!: bexI[where x="(2,4)"])
    show "7 \<in> (\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x})"
      by(auto intro!: bexI[where x="(3,4)"])
    show "8 \<in> (\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x})"
      by(auto intro!: bexI[where x="(4,4)"])
    show "9 \<in> (\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x})"
      by(auto intro!: bexI[where x="(5,4)"])
    show "10 \<in> (\<Union>x\<in>{Suc 0..6} \<times> {Suc 0..6} \<inter> {(x, y). x = 4 \<or> y = 4}. {fst x + snd x})"
      by(auto intro!: bexI[where x="(6,4)"])
  qed auto
   
  have 1:"{Suc 0..6} \<times> {Suc 0..6} \<inter> {x. fst x = 4 \<or> snd x = 4} \<noteq> {}"
  proof - 
    have "(1,4) \<in> {Suc 0..6} \<times> {Suc 0..6} \<inter> {x. fst x = 4 \<or> snd x = 4}"
      by auto
    thus ?thesis by blast
  qed
  hence 2: "set_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) \<inter> {(x, y). x = 4 \<or> y = 4} \<noteq> {}"
    by(auto simp: split_beta')
  have ceq:"condition (die \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s die) (\<lambda>(x,y). x = 4 \<or> y = 4) = qbs_pmf (cond_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x,y). x = 4 \<or> y = 4})"
    by(auto simp: split_beta' qbs_pair_pmf 1 intro!: qbs_pmf_cond_pmf)
  have "two_dice = condition (die \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s die) (\<lambda>(x,y). x = 4 \<or> y = 4) \<bind> (\<lambda>(x,y). return_qbs \<nat>\<^sub>Q (x + y))"
    by(simp add: two_dice_def)
  also have "... = qbs_pmf (cond_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x,y). x = 4 \<or> y = 4}) \<bind> (\<lambda>z. qbs_pmf (return_pmf (fst z + snd z)))"
    by(simp add: ceq) (simp add: qbs_pmf_return_pmf split_beta')
  also have "... = qbs_pmf (cond_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x,y). x = 4 \<or> y = 4} \<bind> (\<lambda>z. return_pmf (fst z + snd z)))"
    by(rule qbs_pmf_bind_pmf[symmetric])
  finally have two_dice_eq:"two_dice = qbs_pmf (cond_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x,y). x = 4 \<or> y = 4} \<bind> (\<lambda>z. return_pmf (fst z + snd z)))" .

  have 3:"measure_pmf.prob (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x, y). x = 4 \<or> y = 4} = 11 / 36"
    using dice_prob1 by(auto simp: split_beta' qbs_pair_pmf)

  have "?P = measure_pmf.prob (cond_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x, y). x = 4 \<or> y = 4} \<bind> (\<lambda>z. return_pmf (fst z + snd z))) {x. P x}" (is "_ = measure_pmf.prob ?bind _")
    by(simp add: two_dice_eq)
  also have "... = measure_pmf.prob ?bind ({x. P x} \<inter> set_pmf ?bind)"
    by(rule measure_Int_set_pmf[symmetric])
  also have "... = sum (pmf ?bind) ({x. P x} \<inter> set_pmf ?bind)"
    by(rule measure_measure_pmf_finite) (auto simp: set_cond_pmf[OF 2])
  also have "... = sum (pmf ?bind) ({x. P x} \<inter> {5, 6, 7, 8, 9, 10})"
    by(auto simp: set_cond_pmf[OF 2] 0)
  also have "... = (\<Sum>n\<in>{n. P n}\<inter>{5, 6, 7, 8, 9, 10}. measure_pmf.expectation (cond_pmf (pair_pmf (pmf_of_set {Suc 0..6}) (pmf_of_set {Suc 0..6})) {(x, y). x = 4 \<or> y = 4}) (\<lambda>x. indicat_real {n} (fst x + snd x)))" (is "_ = (\<Sum>_\<in>_. measure_pmf.expectation ?cond _ )")
    by(simp add: pmf_bind)
  also have "... = (\<Sum>n\<in>{n. P n}\<inter>{5, 6, 7, 8, 9, 10}. (\<Sum>m\<in>{(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(4,1),(4,2),(4,3),(4,5),(4,6)}. indicat_real {n} (fst m + snd m) * pmf ?cond m))"
  proof(intro Finite_Cartesian_Product.sum_cong_aux integral_measure_pmf_real)
    fix n m
    assume h:"n \<in> {n. P n}\<inter>{5, 6, 7, 8, 9, 10}" "m \<in> set_pmf ?cond" "indicat_real {n} (fst m + snd m) \<noteq> 0"
    then have nm:"fst m + snd m = n"
      by(auto simp: indicator_def)
    have m: "fst m \<noteq> 0" "snd m \<noteq> 0" "fst m = 4 \<or> snd m = 4"
      using h(2) by(auto simp: set_cond_pmf[OF 2])
    show "m \<in> {(1, 4), (2, 4), (3, 4), (4,4), (5, 4), (6, 4), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6)}"
      using h(1) nm m by(auto, metis prod.collapse)+
  qed simp
  also have "... = (\<Sum>n\<in>{n. P n}\<inter>{5, 6, 7, 8, 9, 10}. (\<Sum>m\<in>{(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(4,1),(4,2),(4,3),(4,5),(4,6)}. indicat_real {n} (fst m + snd m) * 1 / 11))"
  proof(rule Finite_Cartesian_Product.sum_cong_aux[OF Finite_Cartesian_Product.sum_cong_aux])
    fix n m
    assume h:"n \<in> {n. P n}\<inter>{5, 6, 7, 8, 9, 10}" "m \<in> {(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(4,1),(4,2),(4,3),(4,5),(4::nat,6::nat)}"
    have "pmf ?cond m = 1 / 11"
      using h(2) by(auto simp add: pmf_cond[OF 2] 3 pmf_pair)
    thus " indicat_real {n} (fst m + snd m) * pmf ?cond m = indicat_real {n} (fst m + snd m) * 1 / 11"
      by simp
  qed
  also have "... = ?rp"
    by fastforce
  finally show ?thesis .
qed

corollary
 "\<P>(x in two_dice. x = 5)  = 2 / 11"
 "\<P>(x in two_dice. x = 6)  = 2 / 11"
 "\<P>(x in two_dice. x = 7)  = 2 / 11"
 "\<P>(x in two_dice. x = 8)  = 1 / 11"
 "\<P>(x in two_dice. x = 9)  = 2 / 11"
 "\<P>(x in two_dice. x = 10) = 2 / 11"

  unfolding dice_program_prob by simp_all

subsubsection \<open> Gaussian Mean Learning \<close>
text \<open> Example from Sato et al.~Section~8.~2 in @{cite Sato_2019}.\<close>

definition "Gauss \<equiv> (\<lambda>\<mu> \<sigma>. density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>))"

lemma Gauss_qbs[qbs]: "Gauss \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q"
  by(simp add: Gauss_def)

primrec GaussLearn' :: "[real, real qbs_measure, real list]
                                     \<Rightarrow> real qbs_measure" where
  "GaussLearn' _ p [] = p"
| "GaussLearn' \<sigma> p (y#ls) = query (GaussLearn' \<sigma> p ls)
                                  (normal_density y \<sigma>)"

lemma GaussLearn'_qbs[qbs]:"GaussLearn' \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q \<Rightarrow>\<^sub>Q list_qbs \<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q"
  by(simp add: GaussLearn'_def)

context
  fixes \<sigma> :: real
  assumes [arith]: "\<sigma> > 0"
begin


abbreviation "GaussLearn \<equiv> GaussLearn' \<sigma>"

lemma GaussLearn_qbs[qbs]: "GaussLearn \<in> qbs_space (monadM_qbs \<real>\<^sub>Q \<Rightarrow>\<^sub>Q list_qbs \<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q)"
  by simp

definition Total :: "real list \<Rightarrow> real" where "Total = (\<lambda>l. foldr (+) l 0)"

lemma Total_simp: "Total [] = 0" "Total (y#ls) = y + Total ls"
  by(simp_all add: Total_def)

lemma Total_qbs[qbs]: "Total \<in> list_qbs \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  by(simp add: Total_def)

lemma GaussLearn_Total:
  assumes [arith]: "\<xi> > 0" "n = length L"
  shows "GaussLearn (Gauss \<delta> \<xi>) L = Gauss ((Total L*\<xi>\<^sup>2+\<delta>*\<sigma>\<^sup>2)/(n*\<xi>\<^sup>2+\<sigma>\<^sup>2)) (sqrt ((\<xi>\<^sup>2*\<sigma>\<^sup>2)/(n*\<xi>\<^sup>2+\<sigma>\<^sup>2)))"
  using assms(2)
proof(induction L arbitrary: n)
  case Nil
  then show ?case
    by(simp add: Total_def)
next
  case ih:(Cons a L)
  then obtain n' where n':"n = Suc n'" "n' = length L"
    by auto
  have 1:"\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) > 0"
    by(auto intro!: divide_pos_pos add_nonneg_pos)
  have sigma:"(sqrt (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) * \<sigma> / sqrt (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + \<sigma>\<^sup>2)) = (sqrt (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n * \<xi>\<^sup>2 + \<sigma>\<^sup>2)))"
  proof(rule power2_eq_imp_eq)
    show "(sqrt (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) * \<sigma> / sqrt (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + \<sigma>\<^sup>2))\<^sup>2 = (sqrt (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n * \<xi>\<^sup>2 + \<sigma>\<^sup>2)))\<^sup>2" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) * (\<sigma>\<^sup>2 / (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + \<sigma>\<^sup>2))"
        by (simp add: power_divide power_mult_distrib)
      also have "... = \<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) * (\<sigma>\<^sup>2 / ((\<xi>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + 1) * \<sigma>\<^sup>2))"
        by (simp add: distrib_left mult.commute)
      also have "... = \<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) * (1 / (\<xi>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + 1))"
        by simp
      also have "... = \<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) * (1 / ((\<xi>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)))"
        by(simp only: add_divide_distrib[of "\<xi>\<^sup>2"]) auto
      also have "... = \<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) * ((real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) / (\<xi>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)))"
        by simp
      also have "... = \<xi>\<^sup>2 * \<sigma>\<^sup>2 / (\<xi>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2))"
        using "1" by force
      also have "... = ?rhs"
        by(simp add: n'(1) distrib_right)
      finally show ?thesis .
    qed
  qed simp_all
  have mu: "((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + a * (\<xi>\<^sup>2 * \<sigma>\<^sup>2) / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) / (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + \<sigma>\<^sup>2) = ((a + Total L) * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) / (real n * \<xi>\<^sup>2 + \<sigma>\<^sup>2)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) * \<sigma>\<^sup>2 + a * (\<xi>\<^sup>2 * \<sigma>\<^sup>2))/ (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) / (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + \<sigma>\<^sup>2)"
      by(simp add: add_divide_distrib)
    also have "... = (((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) + a * \<xi>\<^sup>2) * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) / (\<xi>\<^sup>2 * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) + \<sigma>\<^sup>2)"
      by (simp add: distrib_left mult.commute)
    also have "... = (((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) + a * \<xi>\<^sup>2) * \<sigma>\<^sup>2 / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) / ((\<xi>\<^sup>2 * \<sigma>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) * \<sigma>\<^sup>2) / (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2))"
      by (simp add: add_divide_distrib)
    also have "... = (((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) + a * \<xi>\<^sup>2) * \<sigma>\<^sup>2) / (\<xi>\<^sup>2 * \<sigma>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2) * \<sigma>\<^sup>2)"
      using 1 by auto
    also have "... = (((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) + a * \<xi>\<^sup>2) * \<sigma>\<^sup>2) / ((\<xi>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2)) * \<sigma>\<^sup>2)"
      by(simp only: distrib_right)
    also have "... = ((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) + a * \<xi>\<^sup>2) / (\<xi>\<^sup>2 + (real n' * \<xi>\<^sup>2 + \<sigma>\<^sup>2))"
      by simp
    also have "... = ((Total L * \<xi>\<^sup>2 + \<delta> * \<sigma>\<^sup>2) + a * \<xi>\<^sup>2) / (real n * \<xi>\<^sup>2 + \<sigma>\<^sup>2)"
      by(simp add: n'(1) distrib_right)
    also have "... = ?rhs"
      by (simp add: distrib_right)
    finally show ?thesis .
  qed
  show ?case
    by(simp add: ih(1)[OF n'(2)]) (simp add: query_def qbs_normal_posterior[OF real_sqrt_gt_zero[OF 1]] Gauss_def Total_simp sigma mu)
qed

lemma GaussLearn_KL_divergence_lem1:
  fixes a :: real
  assumes [arith]: "a > 0" "b > 0" "c > 0" "d > 0"
  shows "(\<lambda>n. ln ((b * (n * d + c)) / (d * (n * b + a)))) \<longlonglongrightarrow> 0"
proof -
  have "(\<lambda>n::nat. ln ( (b * (Suc n * d + c)) / (d * (Suc n * b + a)))) = (\<lambda>n. ln ( (b * (d + c / Suc n)) / (d * (b + a / Suc n))))"
  proof
    fix n
    show "ln (b * (real (Suc n) * d + c) / (d * (real (Suc n) * b + a))) = ln (b * (d + c / real (Suc n)) / (d * (b + a / real (Suc n))))" (is "ln ?l = ln ?r")
    proof -
      have "?l = b * (d + c / real (Suc n)) / (d * (b + a / real (Suc n))) * (Suc n / Suc n)"
        unfolding times_divide_times_eq distrib_left distrib_right by (simp add: mult.assoc mult.commute)
      also have "... = ?r" by simp
      finally show ?thesis by simp
    qed
  qed
  also have "... \<longlonglongrightarrow> 0"
    apply(rule tendsto_eq_intros(33)[of _ 1])
      apply(rule Topological_Spaces.tendsto_eq_intros(25)[of _ "b * d" _ _ "b * d",OF LIMSEQ_Suc[OF Topological_Spaces.tendsto_eq_intros(18)[of _ b _ _ d]] LIMSEQ_Suc[OF Topological_Spaces.tendsto_eq_intros(18)[of _ d _ _ b]]])
             apply(intro Topological_Spaces.tendsto_eq_intros | auto)+  
    done
  finally show ?thesis
    by(rule LIMSEQ_imp_Suc)
qed

lemma GaussLearn_KL_divergence_lem1':
  fixes b :: real
  assumes [arith]: "b > 0" "d > 0" "s > 0"
  shows "(\<lambda>n. ln (sqrt (b\<^sup>2 * s\<^sup>2 / (real n * b\<^sup>2 + s\<^sup>2)) / sqrt (d\<^sup>2 * s\<^sup>2 / (real n * d\<^sup>2 + s\<^sup>2)))) \<longlonglongrightarrow> 0" (is "?f \<longlonglongrightarrow> 0")
proof -
  have "?f = (\<lambda>n. ln (sqrt ((b\<^sup>2 * (n * d\<^sup>2 + s\<^sup>2))/ (d\<^sup>2 * (n * b\<^sup>2 + s\<^sup>2)))))"
    by(simp add: real_sqrt_divide real_sqrt_mult mult.commute)
  also have "... = (\<lambda>n. ln ((b\<^sup>2 * (n * d\<^sup>2 + s\<^sup>2) / (d\<^sup>2 * (n * b\<^sup>2 + s\<^sup>2)))) / 2)"
    by (standard, rule ln_sqrt) (auto intro!: divide_pos_pos mult_pos_pos add_nonneg_pos)
  also have "... \<longlonglongrightarrow> 0"
    using GaussLearn_KL_divergence_lem1 by auto
  finally show ?thesis .
qed

lemma GaussLearn_KL_divergence_lem2:
  fixes s :: real
  assumes [arith]: "s > 0" "b > 0" "d > 0"
  shows "(\<lambda>n. ((d * s) / (n * d + s)) / (2 * ((b * s) / (n * b + s)))) \<longlonglongrightarrow> 1 / 2"
proof -
  have "(\<lambda>n::nat. ((d * s) / (Suc n * d + s)) / (2 * ((b * s) / (Suc n * b + s)))) = (\<lambda>n. (d * b + d * s / Suc n) / (2 * b * d + 2 * b * s / Suc n))"
  proof
    fix n
    show "d * s / (real (Suc n) * d + s) / (2 * (b * s / (real (Suc n) * b + s))) = (d * b + d * s / real (Suc n)) / (2 * b * d + 2 * b * s / real (Suc n))" (is "?l = ?r")
    proof -
      have "?l = d * (Suc n * b + s) / ((2 * b) * (Suc n * d + s))"
        by(simp add: divide_divide_times_eq)
      also have "... = d * (b + s / Suc n) / ((2 * b) * (d + s / Suc n)) * (Suc n / Suc n)"
      proof -
        have 1:"(2 * b * d * real (Suc n) + 2 * b * (s / real (Suc n)) * real (Suc n))= (2 * b) * (Suc n * d + s)"
          unfolding distrib_left distrib_right by(simp add: mult.assoc mult.commute)
        show ?thesis
          unfolding times_divide_times_eq distrib_left distrib_right 1
          by (simp add: mult.assoc mult.commute)
      qed
      also have "... = ?r"
        by(auto simp:  distrib_right distrib_left mult.commute)
      finally show ?thesis .
    qed
  qed
  also have "... \<longlonglongrightarrow> 1 / 2"
    by(rule Topological_Spaces.tendsto_eq_intros(25)[of _ "d * b" _ _ "2 * b * d",OF LIMSEQ_Suc LIMSEQ_Suc]) (intro Topological_Spaces.tendsto_eq_intros | auto)+
  finally show ?thesis
    by(rule LIMSEQ_imp_Suc)
qed

lemma GaussLearn_KL_divergence_lem2':
  fixes s :: real
  assumes [arith]: "s > 0" "b > 0" "d > 0"
  shows "(\<lambda>n. ((d^2 * s^2) / (n * d^2 + s^2)) / (2 * ((b^2 * s^2) / (n * b^2 + s^2))) - 1 / 2) \<longlonglongrightarrow> 0"
  using GaussLearn_KL_divergence_lem2[of "s^2" "b^2" "d^2"]
  by(rule LIM_zero) auto

lemma GaussLearn_KL_divergence_lem3:
  fixes a b c d s K L :: real
  assumes [arith]: "b > 0" "d > 0" "s > 0"
  shows "((K * d + c * s) / (n * d + s) - (L * b + a * s) / (n * b + s))^2 / (2 * ((b * s) / (n * b + s))) = ((((((K - L) * d * b * real n + c * s * b * real n + K * d * s + c * s * s) - a * s * d * real n - L * b * s - a * s * s))\<^sup>2 / (d * d * b * (real n * real n * real n) + s * s * b * real n + 2 * d * s * b * (real n * real n) + d * d * (real n * real n) * s + s * s * s + 2 * d * s * s * real n))) / (2 * (b * s))" (is "?lhs = ?rhs")
proof -
  have 0:"real n * d + s > 0" "real n * b + s > 0"
    by(auto intro!: add_nonneg_pos)
  hence 1:"real n * d + s \<noteq> 0" "real n * b + s \<noteq> 0" by simp_all
  have "?lhs = (((K * d + c * s) * (n * b + s) - (L * b + a * s) * (n * d + s)) / ((n * d + s) * (n * b + s)))\<^sup>2 / (2 * (b * s / (n * b + s)))"
    unfolding diff_frac_eq[OF 1] by simp
  also have "... = (((((K * d + c * s) * (n * b + s) - (L * b + a * s) * (n * d + s)))\<^sup>2 / ((n * d + s)^2 * (n * b + s)))) / (2 * (b * s))"
    by(auto simp: power2_eq_square)
  also have "... = (((((K * d * (n * b) + c * s * (n * b) + K * d * s + c * s * s) - ((L * b * (n * d) + a * s * (n * d) + L * b * s + a * s * s))))\<^sup>2 / ((n * d)^2 * (n * b) + s^2 * (n * b) + 2 * (n * d) * s * (n * b) + (n * d)^2 * s + s^2 * s + 2 * (n * d) * s * s))) / (2 * (b * s))"
    by(simp add: power2_sum distrib_left distrib_right is_num_normalize(1))
  also have "... = (((((K * d * b * real n + c * s * b * real n + K * d * s + c * s * s) - ((L * b * d * real n + a * s * d * real n + L * b * s + a * s * s))))\<^sup>2 / (d * d * b * (real n * real n * real n) + s * s * b *real n + 2 * d * s * b * (real n * real n) + d * d * (real n * real n) * s + s * s * s + 2 * d * s * s * real n))) / (2 * (b * s))"
    by (simp add: mult.commute mult.left_commute power2_eq_square)
  also have "... = ((((((K - L) * d * b * real n + c * s * b * real n + K * d * s + c * s * s) - ((a * s * d * real n + L * b * s + a * s * s))))\<^sup>2 / (d * d * b * (real n * real n * real n) + s * s * b * real n + 2 * d * s * b * (real n * real n) + d * d * (real n * real n) * s + s * s * s + 2 * d * s * s * real n))) / (2 * (b * s))"
  proof -
    have 1:"K * d * b * real n + c * s * b * real n + K * d * s + c * s * s - (L * b * d * real n + a * s * d * real n + L * b * s +  a * s * s) = (K - L) * d * b * real n + c * s * b * real n + K * d * s +  c * s * s - (a * s * d * real n + L * b * s + a * s * s)"
      by (simp add: left_diff_distrib)
    show ?thesis
      unfolding 1 ..
  qed
  also have "... = ?rhs"
    by (simp add: diff_diff_eq)
  finally show ?thesis .
qed

lemma GaussLearn_KL_divergence_lem4:
  fixes a b c d s K L :: real
  assumes [arith]: "b > 0" "d > 0" "s > 0"
  shows "(\<lambda>n. (\<bar>c * s * b * real n\<bar> + \<bar>K * (real n) * d * s\<bar> + \<bar>c * s * s\<bar> + \<bar>a * s * d * real n\<bar> + \<bar>L * (real n) * b * s\<bar> + \<bar>a * s * s\<bar>)\<^sup>2 / (d * d * b * (real n * real n * real n) + s * s * b * real n + 2 * d * s * b * (real n * real n) + d * d * (real n * real n) * s + s * s * s + 2 * d * s * s * real n) / (2 * (b * s))) \<longlonglongrightarrow> 0" (is "(\<lambda>n. ?f n) \<longlonglongrightarrow> 0")
proof -
  have t1: "(\<lambda>n. x / (real n * real n)) \<longlonglongrightarrow> 0" for x
  proof -
    have "(\<lambda>n. x / (real n * real n)) = (\<lambda>n. x / (real n) * (1 / real n))"
      by simp
    also have "... \<longlonglongrightarrow> 0"
      by (intro Topological_Spaces.tendsto_eq_intros | auto)+
    finally show ?thesis .
  qed
  have t4: "(\<lambda>n. x / (real n * real n * real n)) \<longlonglongrightarrow> 0" for x
  proof -
    have "(\<lambda>n. x / (real n * real n * real n)) = (\<lambda>n. x / (real n) * (1 / real n) * (1 / real n))"
      by simp
    also have "... \<longlonglongrightarrow> 0"
      by (intro Topological_Spaces.tendsto_eq_intros | auto)+
    finally show ?thesis .
  qed
  have t2[tendsto_intros]: "(\<lambda>n. x / (sqrt n)) \<longlonglongrightarrow> 0" for x
    by(rule power_tendsto_0_iff[of 2,THEN iffD1],simp_all add: power2_eq_square) (intro Topological_Spaces.tendsto_eq_intros | auto)+
  have t3: "(\<lambda>n. x / (sqrt n * real n)) \<longlonglongrightarrow> 0" for x
  proof -
    have "(\<lambda>n. x / (sqrt n * real n)) = (\<lambda>n. x / sqrt n * (1 / n))" by simp
    also have "... \<longlonglongrightarrow> 0"
      by (intro Topological_Spaces.tendsto_eq_intros | auto)+
    finally show ?thesis .
  qed

  have "(\<lambda>n. ?f (Suc n)) = (\<lambda>n. ((\<bar>(c * s * b) / sqrt (real (Suc n))\<bar> + \<bar>(K * d * s) / sqrt (real (Suc n))\<bar> + \<bar>(c * s * s) / (sqrt (Suc n) * real (Suc n))\<bar> + \<bar>(a * s * d) / sqrt (real (Suc n))\<bar> + \<bar>(L * b * s) / sqrt (real (Suc n))\<bar> + \<bar>(a * s * s) / (sqrt (Suc n) * real (Suc n))\<bar>)\<^sup>2 / ((d * d * b + (s * s * b) / (real (Suc n) * real (Suc n)) + (2 * d * s * b) / real (Suc n) + (d * d * s) / real (Suc n) + (s * s * s) / (real (Suc n) * real (Suc n) * real (Suc n)) + (2 * d * s * s) / (real (Suc n) * real (Suc n))))) / (2 * (b * s)))" (is "_ = (\<lambda>n. ?g (Suc n))")
  proof
    fix n
    show "?f (Suc n) = ?g (Suc n)"  (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<bar>c * s * b * real (Suc n)\<bar> + \<bar>K * d * s * real (Suc n)\<bar> + \<bar>c * s * s\<bar> + \<bar>a * s * d * real (Suc n)\<bar> + \<bar>L * b * s * real (Suc n)\<bar> + \<bar>a * s * s\<bar>)\<^sup>2 / (d * d * b * (real (Suc n) * real (Suc n) * real (Suc n)) + s * s * b * real (Suc n) + 2 * d * s * b * (real (Suc n) * real (Suc n)) + d * d * (real (Suc n) * real (Suc n)) * s + s * s * s + 2 * d * s * s * real (Suc n)) / (2 * (b * s))"
      proof -
        have 1:"K * real (Suc n) * d * s = K * d * s * real (Suc n)" "L * real (Suc n) * b * s = L * b * s * real (Suc n)"
          by auto
        show ?thesis
          unfolding 1 ..
      qed
      also have "... = ((\<bar>c * s * b / sqrt (real (Suc n))\<bar> + \<bar>K * d * s / sqrt (real (Suc n))\<bar> + \<bar>(c * s * s) / (sqrt (Suc n) * real (Suc n))\<bar> + \<bar>a * s * d / sqrt (real (Suc n))\<bar> + \<bar>L * b * s / sqrt (real (Suc n))\<bar> + \<bar>(a * s * s) / (sqrt (Suc n) * real (Suc n))\<bar>) * (sqrt (Suc n) * real (Suc n)) )\<^sup>2  / (d * d * b * (real (Suc n) * real (Suc n) * real (Suc n)) + s * s * b * real (Suc n) + 2 * d * s * b * (real (Suc n) * real (Suc n)) + d * d * (real (Suc n) * real (Suc n)) * s + s * s * s + 2 * d * s * s * real (Suc n)) / (2 * (b * s))"
        by(simp add: distrib_right left_diff_distrib mult.assoc[symmetric] abs_mult[of _ "real (Suc n)"] del: of_nat_Suc)
      also have "... = ((\<bar>c * s * b / sqrt (real (Suc n))\<bar> + \<bar>K * d * s / sqrt (real (Suc n))\<bar> + \<bar>(c * s * s) / (sqrt (Suc n) * real (Suc n))\<bar> + \<bar>a * s * d / sqrt (real (Suc n))\<bar> + \<bar>L * b * s / sqrt (real (Suc n))\<bar> + \<bar>(a * s * s) / (sqrt (Suc n) * real (Suc n))\<bar>)^2 * (real (Suc n) * real (Suc n) * real (Suc n))) / (d * d * b * (real (Suc n) * real (Suc n) * real (Suc n)) + s * s * b * real (Suc n) + 2 * d * s * b * (real (Suc n) * real (Suc n)) + d * d * (real (Suc n) * real (Suc n)) * s + s * s * s + 2 * d * s * s * real (Suc n)) / (2 * (b * s))"
        by(simp add: power2_eq_square)
      also have "... = ((\<bar>c * s * b / sqrt (real (Suc n))\<bar> + \<bar>K * d * s / sqrt (real (Suc n))\<bar> + \<bar>(c * s * s) / (sqrt (Suc n) * real (Suc n))\<bar> + \<bar>a * s * d / sqrt (real (Suc n))\<bar> + \<bar>L * b * s / sqrt (real (Suc n))\<bar> + \<bar>(a * s * s) / (sqrt (Suc n) * real (Suc n))\<bar>)^2 / ((d * d * b * (real (Suc n) * real (Suc n) * real (Suc n)) + s * s * b * real (Suc n) + 2 * d * s * b * (real (Suc n) * real (Suc n)) + d * d * (real (Suc n) * real (Suc n)) * s + s * s * s + 2 * d * s * s * real (Suc n)) / (real (Suc n) * real (Suc n) * real (Suc n)))) / (2 * (b * s))"
        by simp
      also have "... = ?rhs"
        by(simp add: add_divide_distrib)
      finally show ?thesis .
    qed
  qed
  also have "... \<longlonglongrightarrow> 0"
    apply(rule LIMSEQ_Suc)
    apply(rule Topological_Spaces.tendsto_eq_intros(25)[of _ 0 _ _ "2 * (b * s)",OF Topological_Spaces.tendsto_eq_intros(25)[of _ 0 _ _ "d * d * b"]])
          apply(intro lim_const_over_n t1 t2 t3 t4 tendsto_diff[of _ 0 _ _ 0,simplified] tendsto_add_zero tendsto_add[of _ "d * d * b" _ _ 0,simplified] | auto)+
    done
  finally show ?thesis
    by(rule LIMSEQ_imp_Suc)
qed

lemma GaussLearn_KL_divergence_lem5:
  fixes a b c d K :: real
  assumes [arith]: "b > 0" "d > 0" "s > 0" "K > 0" "\<bar>f l\<bar> < K * length l"
  shows "\<bar>(c * s * b * real (length l) + f l * d * s + c * s * s - a * s * d * real (length l) - f l * b * s - a * s * s)\<^sup>2 / (d * d * b * (real (length l) * real (length l) * real (length l)) + s * s * b * real (length l) + 2 * d * s * b * (real (length l) * real (length l)) + d * d * (real (length l) * real (length l)) * s + s * s * s + 2 * d * s * s * real (length l)) / (2 * (b * s))\<bar> \<le>  \<bar>(\<bar>c * s * b * real (length l)\<bar> + \<bar>K * real (length l) * d * s\<bar> + \<bar>c * s * s\<bar> + \<bar>a * s * d * real (length l)\<bar> + \<bar>- K * real (length l) * b * s\<bar> + \<bar>a * s * s\<bar>)\<^sup>2 / (d * d * b * (real (length l) * real (length l) * real (length l)) + s * s * b * real (length l) + 2 * d * s * b * (real (length l) * real (length l)) + d * d * (real (length l) * real (length l)) * s + s * s * s + 2 * d * s * s * real (length l)) / (2 * (b * s))\<bar>" (is "\<bar>(?l)^2 / ?c1 / ?c2\<bar> \<le> \<bar>(?r)^2 / _ / _\<bar>")
proof -
  have "?l^2 / ?c1 / ?c2 \<le> ?r^2 / ?c1 / ?c2"
  proof(rule divide_right_mono[OF divide_right_mono[OF abs_le_square_iff[THEN iffD1]]])
    show "\<bar>?l\<bar> \<le> \<bar>?r\<bar>"
    proof -
      have "\<bar>?l\<bar> \<le> \<bar>c * s * b * real (length l)\<bar> + \<bar>f l * d * s\<bar> + \<bar>c * s * s\<bar> + \<bar>a * s * d * real (length l)\<bar> + \<bar>f l * b * s\<bar> + \<bar>a * s * s\<bar>"
         by linarith
      also have "... \<le> \<bar>?r\<bar>"
        by (auto simp: mult.assoc abs_mult) (auto intro!: add_mono)
      finally show ?thesis .
    qed
  qed auto
   thus ?thesis
    by fastforce
qed

lemma GaussLearn_KL_divergence_lem6:
  fixes a e b c d K :: real and f :: "'a list \<Rightarrow> real"
  assumes [arith]:"e > 0" "b > 0" "d > 0" "s > 0"
  shows "\<exists>N. \<forall>l. length l \<ge> N \<longrightarrow> \<bar>f l\<bar> < K * length l \<longrightarrow> \<bar>((f l * d + c * s) / (length l * d + s) - (f l * b + a * s) / (length l * b + s))^2 / (2 * ((b * s) / (length l * b + s))) \<bar> < e"
proof(cases "K > 0")
  case K[arith]:True
  from GaussLearn_KL_divergence_lem4[OF assms(2-),of c K a "- K"] assms(1) obtain N where N:
  "\<And>n. n \<ge> N \<Longrightarrow> \<bar>(\<bar>c * s * b * real n\<bar> + \<bar>K * real n * d * s\<bar> + \<bar>c * s * s\<bar> + \<bar>a * s * d * real n\<bar> + \<bar>- K * real n * b * s\<bar> + \<bar>a * s * s\<bar>)\<^sup>2 / (d * d * b * (real n * real n * real n) + s * s * b * real n + 2 * d * s * b * (real n * real n) + d * d * (real n * real n) * s + s * s * s + 2 * d * s * s * real n) / (2 * (b * s))\<bar> < e"
    by(fastforce simp: LIMSEQ_def)
  show ?thesis
  proof(safe intro!: exI[where x=N])
    fix l :: "'a list"
    assume l:"N \<le> length l" "\<bar>f l\<bar> < K * real (length l)"
    show "\<bar>((f l * d + c * s) / (real (length l) * d + s) - (f l * b + a * s) / (real (length l) * b + s))\<^sup>2 / (2 * (b * s / (real (length l) * b + s)))\<bar> < e" (is "?l < _")
    proof -
      have "?l = \<bar>(c * s * b * real (length l) + f l * d * s + c * s * s - a * s * d * real (length l) - f l * b * s - a * s * s)\<^sup>2 / (d * d * b * (real (length l) * real (length l) * real (length l)) + s * s * b * real (length l) + 2 * d * s * b * (real (length l) * real (length l)) + d * d * (real (length l) * real (length l)) * s + s * s * s + 2 * d * s * s * real (length l)) / (2 * (b * s))\<bar>"
        unfolding GaussLearn_KL_divergence_lem3[OF assms(2-)] by simp
      also have "... \<le> \<bar>(\<bar>c * s * b * real (length l)\<bar> + \<bar>K * real (length l) * d * s\<bar> + \<bar>c * s * s\<bar> + \<bar>a * s * d * real (length l)\<bar> + \<bar>- K * real (length l) * b * s\<bar> + \<bar>a * s * s\<bar>)\<^sup>2 / (d * d * b * (real (length l) * real (length l) * real (length l)) + s * s * b * real (length l) + 2 * d * s * b * (real (length l) * real (length l)) + d * d * (real (length l) * real (length l)) * s + s * s * s + 2 * d * s * s * real (length l)) / (2 * (b * s))\<bar>"
        by(rule GaussLearn_KL_divergence_lem5) (use l in auto)
      also have "... < e"
        by(rule N) fact
      finally show ?thesis .
    qed
  qed
next
  case False
  then show ?thesis
    by (metis (no_types, opaque_lifting) abs_ge_zero add_le_cancel_left add_nonneg_nonneg diff_add_cancel diff_ge_0_iff_ge linorder_not_less of_nat_0_le_iff zero_less_mult_iff)
qed

lemma GaussLearn_KL_divergence:
  fixes a b c d e K :: real
  assumes [arith]:"e > 0" "b > 0" "d > 0"
  shows "\<exists>N. \<forall>L. length L > N \<longrightarrow> \<bar>Total L / length L\<bar> < K
          \<longrightarrow> KL_divergence (exp 1) (GaussLearn (Gauss a b) L) (GaussLearn (Gauss c d) L) < e"
proof -
  have h:"\<sigma>^2 > 0" "b^2>0" "d^2>0"
    by auto
  from GaussLearn_KL_divergence_lem6[of "e / 3",OF _ h(2,3,1)] obtain N1 where N1:
  "\<And>l. N1 \<le> length l \<Longrightarrow> \<bar>Total l\<bar> < K * real (length l) \<Longrightarrow> \<bar>((Total l * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length l) * d\<^sup>2 + \<sigma>\<^sup>2) - (Total l * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length l) * b\<^sup>2 + \<sigma>\<^sup>2))\<^sup>2 / (2 *(b\<^sup>2 * \<sigma>\<^sup>2 / (real (length l) * b\<^sup>2 + \<sigma>\<^sup>2)))\<bar> < e / 3"
    by fastforce
  from GaussLearn_KL_divergence_lem1'[OF assms(2,3) \<open>\<sigma> > 0\<close>]
  have "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>n. n \<ge> N \<longrightarrow> \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real n * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real n * d\<^sup>2 + \<sigma>\<^sup>2)))\<bar> < e"
    by(auto simp: LIMSEQ_def)
  from this[of "e / 3"] obtain N2 where N2:
     "\<And>n. n \<ge> N2 \<Longrightarrow> \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real n * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real n * d\<^sup>2 + \<sigma>\<^sup>2)))\<bar> < e / 3"
    by auto
  from GaussLearn_KL_divergence_lem2'[OF \<open>\<sigma> > 0\<close> assms(2,3)]
  have "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>n. n \<ge> N \<longrightarrow> \<bar>d\<^sup>2 * \<sigma>\<^sup>2 / (real n * d\<^sup>2 + \<sigma>\<^sup>2) / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real n * b\<^sup>2 + \<sigma>\<^sup>2))) - 1 / 2\<bar> < e"
    by(auto simp: LIMSEQ_def)
  from this[of "e / 3"] obtain N3 where N3:
    "\<And>n. n \<ge> N3 \<Longrightarrow> \<bar>d\<^sup>2 * \<sigma>\<^sup>2 / (real n * d\<^sup>2 + \<sigma>\<^sup>2) / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real n * b\<^sup>2 + \<sigma>\<^sup>2))) - 1 / 2\<bar> < e / 3"
    by auto
  define N where "N = max (max N1 N2) (max N3 1)"
  have N: "N \<ge> N1" "N \<ge> N2" "N \<ge> N3" "N \<ge> 1"
    by(auto simp: N_def)
  show ?thesis
  proof(safe intro!: exI[where x=N])
    fix L :: "real list"
    assume l:"N < length L" "\<bar>local.Total L / real (length L)\<bar> < K"
    then have l': "N \<le> length L" "\<bar>Total L\<bar> < K * real (length L)"
      using order.strict_trans1[OF N(4) l(1)] by(auto intro!: pos_divide_less_eq[THEN iffD1])
    show "KL_divergence (exp 1) (GaussLearn (Gauss a b) L) (GaussLearn (Gauss c d) L) < e" (is "?lhs < _")
    proof -
      have h': "sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) > 0" "sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)) > 0"
        by(auto intro!: divide_pos_pos add_nonneg_pos)
      have "?lhs \<le> \<bar>?lhs\<bar>"
        by auto
      also have "... = \<bar>KL_divergence (exp 1) (Gauss ((Total L * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)))) (Gauss ((Total L * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)) (sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2))))\<bar>"
        by(simp add: GaussLearn_Total[OF assms(2) refl] GaussLearn_Total[OF assms(3) refl])
      also have "... = \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2))) + ((sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)))\<^sup>2 + ((Total L * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2) - (Total L * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))\<^sup>2) / (2 * (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)))\<^sup>2) - 1 / 2\<bar>"
        by(simp add: KL_normal_density[OF h'] Gauss_def)
      also have "... = \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2))) + (sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)))\<^sup>2 / (2 * (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)))\<^sup>2) + ((Total L * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2) - (Total L * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))\<^sup>2 / (2 * (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)))\<^sup>2) - 1 / 2\<bar>"
        unfolding add_divide_distrib by auto
      also have "... = \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2))) + (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)) / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))) + ((Total L * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2) - (Total L * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))\<^sup>2 / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))) - 1 / 2\<bar>"
        using h' by auto
      also have "... \<le> \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2))) + ((d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)) / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))) - 1 / 2) + ((Total L * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2) - (Total L * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))\<^sup>2 / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)))\<bar>"
        by auto
      also have "... \<le> \<bar>ln (sqrt (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)) / sqrt (d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)))\<bar> + \<bar>(d\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2)) / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))) - 1 / 2\<bar> + \<bar>((Total L * d\<^sup>2 + c * \<sigma>\<^sup>2) / (real (length L) * d\<^sup>2 + \<sigma>\<^sup>2) - (Total L * b\<^sup>2 + a * \<sigma>\<^sup>2) / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2))\<^sup>2 / (2 * (b\<^sup>2 * \<sigma>\<^sup>2 / (real (length L) * b\<^sup>2 + \<sigma>\<^sup>2)))\<bar>"
        by linarith
      also have "... < e"
        using N1[OF order.trans[OF N(1) l'(1)] l'(2)] N2[OF order.trans[OF N(2) l'(1)]] N3[OF order.trans[OF N(3) l'(1)]] by auto
      finally show ?thesis .
    qed
  qed
qed

end

subsubsection \<open> Continuous Distributions \<close>
text \<open> The following (highr-order) program receives a non-negative function $f$ and returns the distribution
       whose density function is (noramlized) $f$ if $f$ is integrable w.r.t. the Lebesgue measure.\<close>
definition dens_to_dist :: "['a :: euclidean_space \<Rightarrow> real] \<Rightarrow> 'a qbs_measure" where
"dens_to_dist \<equiv> (\<lambda>f. do {
                          query lborel\<^sub>Q f
                         })"

lemma dens_to_dist_qbs[qbs]: "dens_to_dist \<in> (borel\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<rightarrow>\<^sub>Q monadM_qbs borel\<^sub>Q"
  by(simp add: dens_to_dist_def)

context
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f_qbs[qbs]: "f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and f_le0:"\<And>x. f x \<ge> 0"
      and f_int_ne0:"qbs_l (density_qbs lborel_qbs f) UNIV \<noteq> 0"
      and f_integrable: "qbs_integrable lborel_qbs f"
begin

lemma f_integrable'[measurable]: "integrable lborel f"
  using f_integrable by(simp add: qbs_integrable_iff_integrable)

lemma f_int_neinfty:
 "qbs_l (density_qbs lborel_qbs f) UNIV \<noteq> \<infinity>"
  using f_integrable' f_le0
  by(auto simp: qbs_l_density_qbs[of _ qbs_borel] emeasure_density integrable_iff_bounded)

lemma dens_to_dist: "dens_to_dist f = density_qbs lborel_qbs (\<lambda>x. ennreal (1 / measure (qbs_l (density_qbs lborel_qbs f)) UNIV * f x))"
proof -
  have [simp]:"ennreal (f x) * (1 / emeasure (qbs_l (density_qbs lborel\<^sub>Q (\<lambda>x. ennreal (f x)))) UNIV) =  ennreal (f x / measure (qbs_l (density_qbs lborel\<^sub>Q (\<lambda>x. ennreal (f x)))) UNIV)" for x
    by (metis divide_ennreal emeasure_eq_ennreal_measure ennreal_0 ennreal_times_divide f_int_ne0 f_int_neinfty f_le0 infinity_ennreal_def mult.comm_neutral zero_less_measure_iff)
  show ?thesis
    by(auto simp: dens_to_dist_def query_def normalize_qbs[of _ qbs_borel,simplified qbs_space_qbs_borel,OF _ f_int_ne0 f_int_neinfty] density_qbs_density_qbs_eq[of _ qbs_borel])
qed

corollary qbs_l_dens_to_dist: "qbs_l (dens_to_dist f) = density lborel (\<lambda>x. ennreal (1 / measure (qbs_l (density_qbs lborel_qbs f)) UNIV * f x))"
  by(simp add: dens_to_dist qbs_l_density_qbs[of _ qbs_borel])

corollary qbs_integral_dens_to_dist:
  assumes [qbs]: "g \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  shows "(\<integral>\<^sub>Q x. g x \<partial>dens_to_dist f) = (\<integral>\<^sub>Q x. 1 / measure (qbs_l (density_qbs lborel_qbs f)) UNIV * f x * g x \<partial>lborel\<^sub>Q)"
  using f_le0 by(simp add: qbs_integral_density_qbs[of _ qbs_borel _ g ,OF _ _ _ AEq_I2[of _ qbs_borel]] dens_to_dist)

lemma dens_to_dist_prob[qbs]:"dens_to_dist f \<in> qbs_space (monadP_qbs borel\<^sub>Q)"
  using f_int_neinfty f_int_ne0 by(auto simp: dens_to_dist_def query_def intro!: normalize_qbs_prob)

end

subsubsection \<open> Normal Distribution \<close>
context
  fixes \<mu> \<sigma> :: real
  assumes sigma_pos[arith]: "\<sigma> > 0"
begin

text \<open> We use an unnormalized density function. \<close>
definition "normal_f \<equiv> (\<lambda>x. exp (-(x - \<mu>)\<^sup>2/ (2 * \<sigma>\<^sup>2)))"

lemma nc_normal_f: "qbs_l (density_qbs lborel_qbs normal_f) UNIV = ennreal (sqrt (2 * pi * \<sigma>\<^sup>2))"
proof -
  have "qbs_l (density_qbs lborel_qbs normal_f) UNIV = (\<integral>\<^sup>+ x. ennreal (exp (- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2)))) \<partial>lborel)"
    by(auto simp: qbs_l_density_qbs[of _ qbs_borel] normal_f_def emeasure_density)
  also have "... = ennreal (sqrt (2 * pi * \<sigma>\<^sup>2)) * (\<integral>\<^sup>+ x. normal_density \<mu> \<sigma> x \<partial>lborel)"
    by(auto simp: nn_integral_cmult[symmetric] normal_density_def ennreal_mult'[symmetric] intro!: nn_integral_cong)
  also have "... = ennreal (sqrt (2 * pi * \<sigma>\<^sup>2))"
    using prob_space.emeasure_space_1[OF prob_space_normal_density]
    by(simp add: emeasure_density)
  finally show ?thesis .
qed

corollary measure_qbs_l_dens_to_dist_normal_f: "measure (qbs_l (density_qbs lborel_qbs normal_f)) UNIV = sqrt (2 * pi * \<sigma>\<^sup>2)"
  by(simp add: measure_def nc_normal_f)


lemma normal_f:
  shows "normal_f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    and "\<And>x. normal_f x \<ge> 0"
    and "qbs_l (density_qbs lborel_qbs normal_f) UNIV \<noteq> 0"
    and "qbs_integrable lborel_qbs normal_f"
  using nc_normal_f by(auto simp: qbs_integrable_iff_integrable integrable_iff_bounded qbs_l_density_qbs[of _ qbs_borel] normal_f_def emeasure_density)

lemma qbs_l_densto_dist_normal_f: "qbs_l (dens_to_dist normal_f) = density lborel (normal_density \<mu> \<sigma>)"
  by(simp add: qbs_l_dens_to_dist[OF normal_f] measure_qbs_l_dens_to_dist_normal_f normal_density_def) (simp add: normal_f_def)

end

subsubsection \<open> Half Normal Distribution \<close>
context
  fixes \<mu> \<sigma> :: real
  assumes sigma_pos[arith]:"\<sigma> > 0"
begin

definition "hnormal_f \<equiv> (\<lambda>x. if x \<le> \<mu> then 0 else normal_density \<mu> \<sigma> x)"

lemma nc_hnormal_f: "qbs_l (density_qbs lborel_qbs hnormal_f) UNIV = ennreal (1/ 2)"
proof -
  have "qbs_l (density_qbs lborel_qbs hnormal_f) UNIV = (\<integral>\<^sup>+ x. ennreal (if x \<le> \<mu> then 0 else normal_density \<mu> \<sigma> x) \<partial>lborel)"
    by(auto simp: qbs_l_density_qbs[of _ qbs_borel] hnormal_f_def emeasure_density)
  also have "... = (\<integral>\<^sup>+ x\<in>{\<mu><..}.  normal_density \<mu> \<sigma> x \<partial>lborel)"
    by(auto intro!: nn_integral_cong)
  also have "... = 1 / 2 * (\<integral>\<^sup>+ x. normal_density \<mu> \<sigma> x \<partial>lborel)"
  proof -
    have 1:"(\<integral>\<^sup>+ x. normal_density \<mu> \<sigma> x \<partial>lborel) = (\<integral>\<^sup>+ x\<in>{\<mu><..}. normal_density \<mu> \<sigma> x \<partial>lborel) + (\<integral>\<^sup>+ x\<in>{..\<mu>}. normal_density \<mu> \<sigma> x \<partial>lborel)"
      by(auto simp: nn_integral_add[symmetric] intro!: nn_integral_cong) (simp add: indicator_def)
    have 2: "(\<integral>\<^sup>+ x\<in>{\<mu><..}. normal_density \<mu> \<sigma> x \<partial>lborel) = (\<integral>\<^sup>+ x\<in>{..\<mu>}. normal_density \<mu> \<sigma> x \<partial>lborel)" (is "?l = ?r")
    proof -
      have "?l = (\<integral>\<^sup>+ x. ennreal (normal_density \<mu> \<sigma> x * indicator {\<mu><..} x) \<partial>lborel)"
        by(auto intro!: nn_integral_cong simp add: indicator_mult_ennreal mult.commute)
      also have "... = ennreal (\<integral>x. normal_density \<mu> \<sigma> x * indicator {\<mu><..} x \<partial>lborel)"
        by(auto intro!: nn_integral_eq_integral integrable_real_mult_indicator)
      also have "... = ennreal (\<integral>x. normal_density \<mu> \<sigma> x * indicator {\<mu><..} x \<partial>lebesgue)"
        by(simp add: integral_completion)
      also have "... = ennreal (\<integral>x. (if x \<in> {\<mu><..} then normal_density \<mu> \<sigma> x else 0) \<partial>lebesgue)"
        by (meson indicator_times_eq_if(2))
      also have "... = ennreal (\<integral>x. normal_density \<mu> \<sigma> x \<partial>lebesgue_on {\<mu><..})"
        by(rule ennreal_cong, rule Lebesgue_Measure.integral_restrict_UNIV) simp
      also have "... = ennreal (integral {\<mu><..} (normal_density \<mu> \<sigma>))"
        by(rule ennreal_cong, rule lebesgue_integral_eq_integral) (auto simp: integrable_restrict_space integrable_completion intro!: integrable_mult_indicator[where 'b=real,simplified])
      also have "... = ennreal (integral {..<\<mu>} (\<lambda>x. normal_density \<mu> \<sigma> (- x + 2 * \<mu>)))"
      proof -
        have "integral {\<mu><..} (normal_density \<mu> \<sigma>) = integral {..<\<mu>} (\<lambda>x. \<bar>- 1\<bar> *\<^sub>R normal_density \<mu> \<sigma> (- x + 2 * \<mu>))"
        proof(rule conjunct2[OF has_absolute_integral_change_of_variables_1'[where g="\<lambda>x. - x + 2 * \<mu>" and S="{..<\<mu>}" and g'="\<lambda>x. - 1" and f="normal_density \<mu> \<sigma>" and b="integral {\<mu><..} (normal_density \<mu> \<sigma>)",THEN iffD2],symmetric])
          fix x :: real
          show "((\<lambda>x. - x + 2 * \<mu>) has_real_derivative - 1) (at x within {..<\<mu>})"
            by(rule derivative_eq_intros(35)[of _ "- 1" _ _ 0]) (auto simp add: Deriv.field_differentiable_minus)
        next
          show "inj_on (\<lambda>x. - x + 2 * \<mu>) {..<\<mu>}"
            by(auto simp: inj_on_def)
        next
          have 1: "(\<lambda>x. - x + 2 * \<mu>) ` {..<\<mu>} = {\<mu><..}"
            by(auto simp: image_def intro!: bexI[where x="2 * \<mu> - _"])
          have [simp]: "normal_density \<mu> \<sigma> absolutely_integrable_on {\<mu><..}"
            by(auto simp: absolutely_integrable_measurable comp_def integrable_restrict_space integrable_completion intro!: integrable_mult_indicator[where 'b=real,simplified] measurable_restrict_space1 measurable_completion)
          show "normal_density \<mu> \<sigma> absolutely_integrable_on (\<lambda>x. - x + 2 * \<mu>) ` {..<\<mu>} \<and> integral ((\<lambda>x. - x + 2 * \<mu>) ` {..<\<mu>}) (normal_density \<mu> \<sigma>) = integral {\<mu><..} (normal_density \<mu> \<sigma>)"
            unfolding 1 by simp
        qed auto
        thus ?thesis by simp
      qed
      also have "... = ennreal (integral {..<\<mu>} (normal_density \<mu> \<sigma>))"
      proof -
        have "(\<lambda>x. normal_density \<mu> \<sigma> (- x + 2 * \<mu>)) = normal_density \<mu> \<sigma>"
          by standard (auto simp: normal_density_def power2_commute )
        thus ?thesis by simp
      qed
      also have "... = ennreal (\<integral>x. normal_density \<mu> \<sigma> x \<partial>lebesgue_on {..<\<mu>})"
        by(rule ennreal_cong, rule lebesgue_integral_eq_integral[symmetric]) (auto simp: integrable_restrict_space integrable_completion intro!: integrable_mult_indicator[where 'b=real,simplified])
      also have "... = ennreal (\<integral>x. (if x \<in> {..<\<mu>} then normal_density \<mu> \<sigma> x else 0) \<partial>lebesgue)"
        by(rule ennreal_cong, rule Lebesgue_Measure.integral_restrict_UNIV[symmetric]) simp
      also have "... =  ennreal (\<integral>x. normal_density \<mu> \<sigma> x * indicator {..<\<mu>} x \<partial>lebesgue)"
        by (meson indicator_times_eq_if(2)[symmetric])
      also have "... = ennreal (\<integral>x. normal_density \<mu> \<sigma> x * indicator {..<\<mu>} x \<partial>lborel)"
        by(simp add: integral_completion)
      also have "... = (\<integral>\<^sup>+ x. ennreal (normal_density \<mu> \<sigma> x * indicator {..<\<mu>} x) \<partial>lborel)"
        by(auto intro!: nn_integral_eq_integral[symmetric] integrable_real_mult_indicator)
      also have "... = ?r"
        using AE_lborel_singleton by(fastforce intro!: nn_integral_cong_AE simp: indicator_def)
      finally show ?thesis .
    qed
    show ?thesis
      by(simp add: 1 2) (metis (no_types, lifting) ennreal_divide_times mult_2 mult_2_right mult_divide_eq_ennreal one_add_one top_neq_numeral zero_neq_numeral)
  qed
  also have "... = ennreal (1 / 2)"
    using prob_space.emeasure_space_1[OF prob_space_normal_density]
    by(simp add: emeasure_density divide_ennreal_def)
  finally show ?thesis .
qed

corollary measure_qbs_l_dens_to_dist_hnormal_f: "measure (qbs_l (density_qbs lborel_qbs hnormal_f)) UNIV = 1 / 2"
  by(simp add: measure_def nc_hnormal_f del: ennreal_half)

lemma hnormal_f:
  shows "hnormal_f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    and "\<And>x. hnormal_f x \<ge> 0"
    and "qbs_l (density_qbs lborel_qbs hnormal_f) UNIV \<noteq> 0"
    and "qbs_integrable lborel_qbs hnormal_f"
  using nc_hnormal_f by(auto simp: qbs_integrable_iff_integrable integrable_iff_bounded qbs_l_density_qbs[of _ qbs_borel] hnormal_f_def emeasure_density simp del: ennreal_half)

lemma "qbs_l (dens_to_dist local.hnormal_f) = density lborel (\<lambda>x. ennreal (2 * (if x \<le> \<mu> then 0 else normal_density \<mu> \<sigma> x)))"
  by(simp add: qbs_l_dens_to_dist[OF hnormal_f] measure_qbs_l_dens_to_dist_hnormal_f) (simp add: hnormal_f_def)

end


subsubsection \<open> Erlang Distribution \<close>
context
  fixes k :: nat and l :: real
  assumes l_pos[arith]: "l > 0"
begin

definition "erlang_f \<equiv> (\<lambda>x. if x < 0 then 0 else x^k * exp (- l * x))"

lemma nc_erlang_f: "qbs_l (density_qbs lborel_qbs erlang_f) UNIV = ennreal (fact k / l^(Suc k))"
proof -
  have "qbs_l (density_qbs lborel_qbs erlang_f) UNIV = (\<integral>\<^sup>+ x. ennreal (if x < 0 then 0 else x ^ k * exp (- l * x)) \<partial>lborel)"
    by(auto simp: qbs_l_density_qbs[of _ qbs_borel] erlang_f_def emeasure_density)
  also have "... = ennreal (fact k / l^(Suc k)) * (\<integral>\<^sup>+ x. erlang_density k l x \<partial>lborel)"
    by(auto simp: nn_integral_cmult[symmetric] ennreal_mult'[symmetric] erlang_density_def intro!: nn_integral_cong)
  also have "... = ennreal (fact k / l^(Suc k))"
    using prob_space.emeasure_space_1[OF prob_space_erlang_density]
    by(simp add: emeasure_density)
  finally show ?thesis .
qed

corollary measure_qbs_l_dens_to_dist_erlang_f: "measure (qbs_l (density_qbs lborel_qbs erlang_f)) UNIV = fact k / l^(Suc k)"
  by(simp add: measure_def nc_erlang_f)

lemma erlang_f:
  shows "erlang_f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    and "\<And>x. erlang_f x \<ge> 0"
    and "qbs_l (density_qbs lborel_qbs erlang_f) UNIV \<noteq> 0"
    and "qbs_integrable lborel_qbs erlang_f"
  using nc_erlang_f by(auto simp: qbs_integrable_iff_integrable integrable_iff_bounded qbs_l_density_qbs[of _ qbs_borel] erlang_f_def emeasure_density)

lemma "qbs_l (dens_to_dist erlang_f) = density lborel (erlang_density k l)"
proof -
  have [simp]: "l * l ^ k * (if x < 0 then 0 else x ^ k * exp (- l * x)) / fact k = (if x < 0 then 0 else l ^ Suc k * x ^ k * exp (- l * x) / fact k)" for x
    by auto
  show ?thesis
    by(simp add: qbs_l_dens_to_dist[OF erlang_f] measure_qbs_l_dens_to_dist_erlang_f erlang_density_def) (simp add: erlang_f_def)
qed

end

subsubsection \<open> Uniform Distribution on $(0,1) \times (0,1)$.\<close>

definition "uniform_f \<equiv> indicat_real ({0<..<1::real}\<times>{0<..<1::real})"

lemma
  shows uniform_f_qbs'[qbs]: "uniform_f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    and uniform_f_qbs[qbs]: "uniform_f \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
proof -
  have "uniform_f \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    by(auto simp: uniform_f_def r_preserves_product[symmetric] intro!: rr.qbs_morphism_measurable_intro)
  thus "uniform_f \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q" "uniform_f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    by(simp_all add: qbs_borel_prod)
qed

lemma uniform_f_measurable[measurable]: "uniform_f \<in> borel_measurable borel"
  by (metis borel_prod rr.standard_borel_axioms standard_borel.standard_borel_r_full_faithful uniform_f_qbs')

lemma nc_uniform_f: "qbs_l (density_qbs lborel_qbs uniform_f) UNIV = 1"
proof -
  have "qbs_l (density_qbs lborel_qbs uniform_f) UNIV = (\<integral>\<^sup>+ z. ennreal (uniform_f z) \<partial>lborel)"
    by(auto simp: qbs_l_density_qbs[of _ qbs_borel] emeasure_density)
  also have "... = (\<integral>\<^sup>+ z. indicator {0<..<1::real} (fst z) * indicator {0<..<1::real} (snd z) \<partial>(lborel \<Otimes>\<^sub>M lborel))"
    by(auto simp: lborel_prod intro!: nn_integral_cong) (auto simp: indicator_def uniform_f_def)
  also have "... = 1"
    by(auto simp: lborel.nn_integral_fst[symmetric] nn_integral_cmult)
  finally show ?thesis .
qed

corollary measure_qbs_l_dens_to_dist_uniform_f: "measure (qbs_l (density_qbs lborel_qbs uniform_f)) UNIV = 1"
  by(simp add: measure_def nc_uniform_f)

lemma uniform_f:
  shows "uniform_f \<in> qbs_borel \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    and "\<And>x. uniform_f x \<ge> 0"
    and "qbs_l (density_qbs lborel_qbs uniform_f) UNIV \<noteq> 0"
    and "qbs_integrable lborel_qbs uniform_f"
  using nc_uniform_f by(auto simp: qbs_integrable_iff_integrable integrable_iff_bounded qbs_l_density_qbs[of _ qbs_borel] emeasure_density) (auto simp: uniform_f_def)

lemma qbs_l_dens_to_dist_uniform_f:"qbs_l (dens_to_dist uniform_f) = density lborel (\<lambda>x. ennreal (uniform_f x))"
  by(simp add: qbs_l_dens_to_dist[OF uniform_f,simplified measure_qbs_l_dens_to_dist_uniform_f])

lemma "dens_to_dist uniform_f = Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1"
proof -
  note qbs_pair_measure_morphismP[qbs] Uniform_qbsP[qbs]
  have [simp]:"sets (borel :: (real \<times> real) measure) = sets (borel \<Otimes>\<^sub>M borel)"
    by(metis borel_prod)
  show ?thesis
  proof(safe intro!: inj_onD[OF qbs_l_inj[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q"]] qbs_space_monadPM measure_eqI)
(*  proof(auto intro!: inj_onD[OF qbs_l_inj[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q"]] qbs_space_monadPM simp: qbs_l_dens_to_dist_uniform_f qbs_l_Uniform_pair, auto intro!: measure_eqI)
 *)
    fix A :: "(real \<times> real) set"
    assume "A \<in> sets (qbs_l (dens_to_dist uniform_f))"
    then have [measurable]: "A \<in> sets (borel \<Otimes>\<^sub>M borel)"
      by(auto simp: qbs_l_dens_to_dist_uniform_f)
    show "emeasure (qbs_l (dens_to_dist uniform_f)) A = emeasure (qbs_l (Uniform 0 1 \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s Uniform 0 1)) A" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>\<^sup>+x\<in>A. ennreal (uniform_f x) \<partial>(lborel \<Otimes>\<^sub>M lborel))"
        by(simp add: emeasure_density lborel_prod qbs_l_dens_to_dist_uniform_f)
      also have "... = (\<integral>\<^sup>+x. indicator A x * indicator {0<..<1} (fst x) * indicator {0<..<1} (snd x) \<partial>(lborel \<Otimes>\<^sub>M lborel))"
        by(auto intro!: nn_integral_cong) (auto simp: indicator_def uniform_f_def)
      also have "... = (\<integral>\<^sup>+ x\<in>{0<..<1}. (\<integral>\<^sup>+y\<in>{0<..<1}. indicator A (x, y) \<partial>lborel) \<partial>lborel)"
        by(auto simp add: lborel.nn_integral_fst[symmetric] intro!: nn_integral_cong) (auto simp: indicator_def)
      also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator A (x, y) \<partial>uniform_measure lborel {0<..<1}) \<partial>uniform_measure lborel {0<..<1})"
        by(auto simp: nn_integral_uniform_measure divide_ennreal_def)
      also have "... = ?rhs"
        by(auto simp: UniformP_pair.M1.emeasure_pair_measure' qbs_l_Uniform_pair)
      finally show ?thesis .
    qed
  next
    show "dens_to_dist uniform_f \<in> qbs_space (monadP_qbs (\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q))"
      by(simp add: dens_to_dist_prob[OF uniform_f] qbs_borel_prod)
  qed (auto simp: qbs_l_dens_to_dist_uniform_f qbs_l_Uniform_pair, qbs, simp)
qed

subsubsection \<open> If then else \<close>

definition gt :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool qbs_measure" where
"gt \<equiv> (\<lambda>f r. do {
                  x \<leftarrow> dens_to_dist (normal_f 0 1);
                  if f x > r
                  then return_qbs \<bool>\<^sub>Q True
                  else return_qbs \<bool>\<^sub>Q False
                  })"

declare normal_f(1)[of 1 0,simplified]

lemma gt_qbs[qbs]: "gt \<in> qbs_space ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadP_qbs \<bool>\<^sub>Q)"
proof -
  note [qbs] = dens_to_dist_prob[OF normal_f[of 1 0,simplified]] bind_qbs_morphismP return_qbs_morphismP
  show ?thesis
    by(simp add: gt_def)
qed

lemma
  assumes [qbs]: "f \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  shows "\<P>(b in gt f r. b = True) = \<P>(x in std_normal_distribution. f x > r)" (is "?P1 = ?P2")
proof -
  note [qbs] = dens_to_dist_prob[OF normal_f[of 1 0,simplified]] bind_qbs_morphismP return_qbs_morphismP
  have 1[simp]: "space (qbs_l (gt f r)) = UNIV"
    by(simp add: space_qbs_l_in[OF qbs_space_monadPM,of _ "\<bool>\<^sub>Q"])
  have "?P1 = (\<integral>b. indicat_real {True} b \<partial>qbs_l (gt f r))"
    by simp (metis (full_types) Collect_cong singleton_conv2)
  also have "... = (\<integral>\<^sub>Q b. indicat_real {True} b \<partial>(gt f r))"
    by(simp add: qbs_integral_def2_l)
  also have "... = (\<integral>\<^sub>Q b. indicat_real {True} b \<partial>(dens_to_dist (normal_f 0 1) \<bind> (\<lambda>x. return_qbs \<bool>\<^sub>Q (f x > r))))"
  proof -
    have [simp]:"gt f r = dens_to_dist (normal_f 0 1) \<bind> (\<lambda>x. return_qbs \<bool>\<^sub>Q (f x > r))"
      by(auto simp: gt_def intro!: bind_qbs_cong[of _ "\<real>\<^sub>Q" _ _ "\<bool>\<^sub>Q"] qbs_space_monadPM qbs_morphism_monadPD)
    show ?thesis by simp
  qed
  also have "... = (\<integral>\<^sub>Q x. (indicat_real {True} \<circ> (\<lambda>x. f x > r)) x \<partial>dens_to_dist (normal_f 0 1))"
    by(rule qbs_integral_bind_return[of _ "\<real>\<^sub>Q"]) (auto intro!: qbs_space_monadPM)
  also have "... = (\<integral>\<^sub>Q x. indicat_real {x. f x > r} x \<partial>dens_to_dist (normal_f 0 1))"
    by(auto intro!: qbs_integral_cong[of _ "\<real>\<^sub>Q"] qbs_space_monadPM simp: indicator_def)
  also have "... = (\<integral>x. indicat_real {x. f x > r} x \<partial>dens_to_dist (normal_f 0 1))"
    by(simp add: qbs_integral_def2_l)
  also have "... = ?P2"
    by(simp add: qbs_l_densto_dist_normal_f[of 1 0])
  finally show ?thesis .
qed

text \<open>Examples from Staton~\cite[Sect.~2.2]{staton_2020}.\<close>
subsubsection \<open> Weekend \<close>
text \<open> Example from Staton~\cite[Sect.~2.2.1]{staton_2020}.\<close>
text \<open> This example is formalized in Coq by Affeldt et al.~\cite{10.1145/3573105.3575691}.\<close>
definition weekend :: "bool qbs_measure" where
"weekend \<equiv> do {
             let x = qbs_bernoulli (2 / 7);
                 f = (\<lambda>x. let r = if x then 3 else 10 in pmf (poisson_pmf r) 4)
             in query x f
              }"

lemma weekend_qbs[qbs]:"weekend \<in> qbs_space (monadM_qbs \<bool>\<^sub>Q)"
  by(simp add: weekend_def)

lemma weekend_nc:
  defines "N \<equiv> 2 / 7 * pmf (poisson_pmf 3) 4  + 5 / 7 *  pmf (poisson_pmf 10) 4"
  shows "qbs_l (density_qbs (bernoulli_pmf (2/7)) (\<lambda>x. (pmf (poisson_pmf (if x then 3 else 10)) 4))) UNIV = N" 
proof -
  have [simp]:"fact 4 = 4 * fact 3"
    by (simp add: fact_numeral)
  show ?thesis
    by(simp add: qbs_l_density_qbs[of _ "\<bool>\<^sub>Q"] emeasure_density ennreal_plus[symmetric] ennreal_mult'[symmetric] N_def del: ennreal_plus)
qed

lemma qbs_l_weekend:
  defines "N \<equiv> 2 / 7 * pmf (poisson_pmf 3) 4  + 5 / 7 *  pmf (poisson_pmf 10) 4"
  shows "qbs_l weekend = qbs_l (density_qbs (qbs_bernoulli (2 / 7)) (\<lambda>x. ennreal (let r = if x then 3 else 10 in r ^ 4 * exp (- r) / (fact 4 * N))))" (is "?lhs = ?rhs")
proof -
  have [simp]: "N > 0"
    by(auto simp: N_def intro!: add_pos_pos)
  have "?lhs = qbs_l (density_qbs (density_qbs (qbs_bernoulli (2 / 7)) (\<lambda>x. ennreal (let r = if x then 3 else 10 in r ^ 4 * exp (- r) / fact 4))) (\<lambda>x. 1 /  ennreal N))"
    using normalize_qbs[of "density_qbs (qbs_bernoulli (2/7)) (\<lambda>x. (pmf (poisson_pmf (if x then 3 else 10)) 4))" "\<bool>\<^sub>Q",simplified] weekend_nc
    by(simp add: weekend_def query_def N_def Let_def)
  also have "... = ?rhs"
    by(simp add: density_qbs_density_qbs_eq[of _ "\<bool>\<^sub>Q"] ennreal_mult'[symmetric] ennreal_1[symmetric] divide_ennreal del: ennreal_1) (metis (mono_tags, opaque_lifting) divide_divide_eq_left)
  finally show ?thesis .
qed

lemma
  defines "N \<equiv> 2 / 7 * pmf (poisson_pmf 3) 4  + 5 / 7 *  pmf (poisson_pmf 10) 4"
  shows "\<P>(b in weekend. b = True) = 2 / 7 * (3^4 * exp (- 3)) / fact 4 * 1 / N"
  by simp (simp add: qbs_l_weekend measure_def qbs_l_density_qbs[of _ "\<bool>\<^sub>Q"] emeasure_density emeasure_measure_pmf_finite ennreal_mult'[symmetric] N_def)


subsubsection \<open> Whattime \<close>
text \<open> Example from Staton~\cite[Sect.~2.2.3]{staton_2020}\<close>
text \<open> $f$ is given as a parameter.\<close>
definition whattime :: "(real \<Rightarrow> real) \<Rightarrow> real qbs_measure" where
"whattime \<equiv> (\<lambda>f. do {
                       let T = Uniform 0 24 in
                       query T (\<lambda>t. let r = f t in
                                    exponential_density r (1 / 60))
                     })"

lemma whattime_qbs[qbs]: "whattime \<in> (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q"
  by(simp add: whattime_def)

lemma qbs_l_whattime_sub:
  assumes [qbs]: "f \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q"
  shows "qbs_l (density_qbs (Uniform 0 24) (\<lambda>x. exponential_density (f x) (1 / 60))) = density lborel (\<lambda>x. indicator {0<..<24} x / 24 * exponential_density (f x) (1 / 60))"
proof -
  have [measurable]:"f \<in> borel_measurable borel"
    by (simp add: standard_borel.standard_borel_r_full_faithful standard_borel_ne.standard_borel)
  have [measurable]: "(\<lambda>x. (exponential_density (f x) (1 / 60))) \<in> borel_measurable borel"
    by(simp add: exponential_density_def)
  have 1[measurable]: "(\<lambda>x. ennreal (exponential_density (f x) (1 / 60))) \<in> borel_measurable (uniform_measure lborel {0<..<24})"
    by(simp add: measurable_cong_sets[OF sets_uniform_measure])
  show ?thesis
    by(auto simp: qbs_l_density_qbs[of _ qbs_borel] emeasure_density emeasure_density[OF 1] nn_integral_uniform_measure nn_integral_divide[symmetric] ennreal_mult' divide_ennreal[symmetric] intro!: measure_eqI  nn_integral_cong simp del: times_divide_eq_left)
      (simp add: ennreal_indicator ennreal_times_divide mult.commute mult.left_commute)
qed

lemma
  assumes [qbs]: "f \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q" and [measurable]:"U \<in> sets borel"
      and "\<And>r. f r \<ge> 0"
  defines "N \<equiv> (\<integral>t\<in>{0<..<24}. (f t * exp (- 1/ 60 * f t)) \<partial>lborel)"
  defines "N' \<equiv> (\<integral>\<^sup>+t\<in>{0<..<24}. (f t * exp (- 1/ 60 * f t)) \<partial>lborel)"
  assumes "N' \<noteq> 0" and "N' \<noteq> \<infinity>"
  shows "\<P>(t in whattime f. t \<in> U) = (\<integral>t\<in>{0<..<24}\<inter>U. (f t * exp (- 1/ 60 * f t)) \<partial>lborel) / N"
proof -
  have 1: "space (whattime f) = UNIV"
    by (rule space_qbs_l_in[of "whattime f" "\<real>\<^sub>Q",simplified qbs_space_qbs_borel]) simp
  have [measurable]: "f \<in> borel_measurable borel"
    by (simp add: standard_borel.standard_borel_r_full_faithful standard_borel_ne.standard_borel)
  have [measurable]: "(\<lambda>x. exponential_density (f x) (1 / 60)) \<in> borel_measurable borel"
    by(simp add: measurable_cong_sets[OF sets_uniform_measure] exponential_density_def)
  have [measurable]: "(\<lambda>x. ennreal (exponential_density (f x) (1 / 60))) \<in> borel_measurable (uniform_measure lborel {0<..<24})"
    by(simp add: measurable_cong_sets[OF sets_uniform_measure])
  have qbs_ld: "qbs_l (density_qbs (Uniform 0 24) (\<lambda>x. exponential_density (f x) (1 / 60))) UNIV = (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x) / 24) \<partial>lborel)"
    by(auto simp: qbs_l_whattime_sub emeasure_density intro!: nn_integral_cong,auto simp: ennreal_indicator[symmetric]  ennreal_mult''[symmetric] exponential_density_def) (simp add: mult.commute)
  have int: "integrable lborel (\<lambda>x. f x * exp (- 1/ 60 * f x) * indicat_real {0<..<24} x)"
    using assms(3,7) by(simp add: N'_def integrable_iff_bounded ennreal_mult'' ennreal_indicator top.not_eq_extremum)

  have ge: "(\<integral>x\<in>{0<..<24}. (f x * exp (- (f x / 60)) / 24)\<partial>lborel) > 0"
  proof -
    have "(\<integral>x\<in>{0<..<24}. (f x * exp (- (f x / 60))) \<partial>lborel) > 0" (is "?l > 0")
    proof -
      have "ennreal ?l = (\<integral>\<^sup>+x. (indicator {0<..<24} x * (f x * exp (- (f x / 60)))) \<partial>lborel)"
        unfolding set_lebesgue_integral_def by(simp,rule nn_integral_eq_integral[symmetric]) (insert int assms(3),auto simp: mult.commute)
      also have "... = (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x)) \<partial>lborel)"
        by (simp add: indicator_mult_ennreal mult.commute)
      also have "... > 0"
        using assms(6) not_gr_zero N'_def by blast
      finally show ?thesis
        using ennreal_less_zero_iff by blast
    qed
    thus ?thesis by simp
  qed
  have ge2: "(\<integral>x\<in>{0<..<24}\<inter> U. (exponential_density (f x) (1 / 60)) \<partial>lborel) \<ge> 0"
    using assms(3) by(auto intro!: integral_nonneg_AE simp: set_lebesgue_integral_def)

  have "(\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x) / 24) \<partial>lborel) \<noteq> 0 \<and> (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x) / 24) \<partial>lborel) \<noteq> \<infinity>"
  proof -
    have "(\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x) / 24) \<partial>lborel) = (\<integral>\<^sup>+x. ennreal (f x * exp (- 1/ 60 * f x)) * indicator {0<..<24} x / 24 \<partial>lborel)"
      by(rule nn_integral_cong, insert assms(3)) (auto simp: divide_ennreal[symmetric] ennreal_times_divide mult.commute)
    also have "... = (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x)) \<partial>lborel) / 24"
      by(simp add: nn_integral_divide)
    finally show ?thesis
      using assms(5,6,7) by (simp add: ennreal_divide_eq_top_iff)
  qed
  hence "normalize_qbs (density_qbs (Uniform 0 24) (\<lambda>x. (exponential_density (f x) (1 / 60)))) = density_qbs (density_qbs (Uniform 0 24) (\<lambda>x. ennreal (exponential_density (f x) (1 / 60)))) (\<lambda>x. 1 / (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- 1/ 60 * f x) / 24) \<partial>lborel))"
    using normalize_qbs[of "density_qbs (Uniform 0 24) (\<lambda>x. exponential_density (f x) (1 / 60))" qbs_borel,simplified] by(simp add: qbs_ld)
  also have "... = density_qbs (Uniform 0 24) (\<lambda>x. ennreal (exponential_density (f x) (1 / 60)) / (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- (f x / 60)) / 24) \<partial>lborel))"
    by(simp add: density_qbs_density_qbs_eq[of _ qbs_borel] ennreal_times_divide)
 
  finally have "\<P>(x in whattime f. x \<in> U) = measure (density (qbs_l (Uniform 0 24)) (\<lambda>x. ennreal (exponential_density (f x) (1 / 60)) / (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- (f x / 60)) / 24) \<partial>lborel))) U"
    unfolding 1 by (simp add: whattime_def query_def qbs_l_density_qbs[of _ qbs_borel])
  also have "... = enn2real ((\<integral>\<^sup>+x\<in>{0<..<24}. (ennreal (exponential_density (f x) (1 / 60)) / (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- (f x / 60)) / 24)\<partial>lborel) * indicator U x) \<partial>lborel) / 24)"
    by(simp add: measure_def emeasure_density nn_integral_uniform_measure)
  also have "... = enn2real ((\<integral>\<^sup>+x\<in>{0<..<24}. (ennreal (exponential_density (f x) (1 / 60)) * indicator U x) \<partial>lborel) /  (\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- (f x / 60)) / 24)\<partial>lborel) / 24)"
    by(simp add:  ennreal_divide_times ennreal_times_divide nn_integral_divide)
  also have "... = enn2real (ennreal (\<integral>x\<in>{0<..<24}\<inter> U. (exponential_density (f x) (1 / 60)) \<partial>lborel) /  ennreal (\<integral>x\<in>{0<..<24}. (f x * exp (- (f x / 60)) / 24)\<partial>lborel) / ennreal 24)"
  proof -
    have 1:"(\<integral>\<^sup>+x\<in>{0<..<24}. ennreal (f x * exp (- (f x / 60)) / 24)\<partial>lborel) = ennreal (\<integral>x\<in>{0<..<24}. (f x * exp (- (f x / 60)) / 24)\<partial>lborel)" (is "?l = ?r")
    proof -
      have "?l = (\<integral>\<^sup>+x. ennreal (f x * exp (- (f x / 60)) / 24 * indicat_real {0<..<24} x) \<partial>lborel)"
        by (simp add: nn_integral_set_ennreal)
      also have "... = ennreal (\<integral>x. (f x * exp (- (f x / 60)) / 24 * indicat_real {0<..<24} x)\<partial>lborel)"
        by(rule nn_integral_eq_integral) (use int assms(3) in auto)
      also have "... = ?r"
        by(auto simp: set_lebesgue_integral_def intro!: Bochner_Integration.integral_cong ennreal_cong)
      finally show ?thesis .
    qed
    have 2:"(\<integral>\<^sup>+x\<in>{0<..<24}. (ennreal (exponential_density (f x) (1 / 60)) * indicator U x) \<partial>lborel) = ennreal (\<integral>x\<in>{0<..<24}\<inter> U. (exponential_density (f x) (1 / 60)) \<partial>lborel)" (is "?l = ?r")
    proof -
      have "?l = (\<integral>\<^sup>+x. ennreal (f x * exp (- (f x / 60)) * indicat_real {0<..<24} x * indicator U x) \<partial>lborel)"
        by (auto intro!: nn_integral_cong simp: exponential_density_def indicator_def)
      also have "... = ennreal (\<integral>x. (f x * exp (- (f x / 60)) * indicat_real {0<..<24} x * indicator U x)\<partial>lborel)"
        by(rule nn_integral_eq_integral) (use integrable_real_mult_indicator[OF _ int] assms(3)  in auto)
      also have "... = ?r"
        by(auto simp: set_lebesgue_integral_def indicator_def exponential_density_def intro!: Bochner_Integration.integral_cong ennreal_cong)
      finally show ?thesis .
    qed
    show ?thesis
      by(simp add: 1 2)
  qed
  also have "... = enn2real (ennreal ((\<integral>x\<in>{0<..<24}\<inter> U. (exponential_density (f x) (1 / 60)) \<partial>lborel) / (\<integral>x\<in>{0<..<24}. (f x * exp (- (f x / 60)) / 24)\<partial>lborel) / 24))"
    by(simp only: divide_ennreal[OF ge2 ge] divide_ennreal[OF divide_nonneg_pos[OF ge2 ge]])
  also have "... = (\<integral>x\<in>{0<..<24}\<inter> U. (exponential_density (f x) (1 / 60)) \<partial>lborel) / (\<integral>x\<in>{0<..<24}. (f x * exp (- (f x / 60)) / 24)\<partial>lborel) / 24"
    by(rule enn2real_ennreal) (use ge ge2 in auto)
  also have "... = (\<integral>x\<in>{0<..<24}\<inter>U. (f x * exp (- 1/ 60 * f x)) \<partial>lborel) / N"
    by(auto simp: N_def exponential_density_def)
  finally show ?thesis .
qed

subsubsection \<open> Distributions on Functions \<close>
definition a_times_x :: "(real \<Rightarrow> real) qbs_measure" where
"a_times_x \<equiv> do {
                  a \<leftarrow> Uniform (-2) 2;
                  return_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) (\<lambda>x. a * x)
                 }"

lemma a_times_x_qbs[qbs]: "a_times_x \<in> monadM_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q)"
  by(simp add: a_times_x_def)

lemma a_times_x_qbsP: "a_times_x \<in> monadP_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q)"
proof -
  note [qbs] = Uniform_qbsP[of "-2" 2,simplified] return_qbs_morphismP bind_qbs_morphismP
  show ?thesis
    by(simp add: a_times_x_def)
qed

definition a_times_x' :: "(real \<Rightarrow> real) qbs_measure" where
"a_times_x' \<equiv> do {
                  condition a_times_x (\<lambda>f. f 1 \<ge> 0)
                 }"

lemma a_times_x'_qbs[qbs]: "a_times_x' \<in> monadM_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q)"
  by(simp add: a_times_x'_def)

lemma prob_a_times_x:
  assumes [measurable]: "Measurable.pred borel P"
  shows "\<P>(f in a_times_x. P (f r)) = \<P>(a in Uniform (-2) 2. P (a * r))" (is "?lhs = ?rhs")
proof -
  have [qbs]: "qbs_pred qbs_borel P"
    using r_preserves_morphisms by fastforce
  have "?lhs = measure a_times_x ({f. P (f r)} \<inter> space a_times_x)"
    by (simp add: Collect_conj_eq inf_sup_aci(1))
  also have "... = (\<integral>\<^sub>Q f. indicat_real {f. P (f r)} f \<partial>a_times_x)"
    by(simp add: qbs_integral_def2_l)
  also have "... = qbs_integral (Uniform (- 2) 2) (indicat_real {f. P (f r)} \<circ> (*))"
    unfolding a_times_x_def by(rule qbs_integral_bind_return[of _ qbs_borel]) auto
  also have "... = (\<integral>\<^sub>Q a. indicat_real {a. P (a * r)} a \<partial>Uniform (- 2) 2)"
    by(auto simp: comp_def indicator_def)
  also have "... = ?rhs"
    by (simp add: qbs_integral_def2_l)
  finally show ?thesis .
qed

lemma "\<P>(f in a_times_x'. f 1 \<ge> 1) = 1 / 2" (is "?P = _")
proof -
  have "?P = \<P>(f in a_times_x. f 1 \<ge> 1 \<bar> f 1 \<ge> 0)"
    by(simp add: query_Bayes[OF a_times_x_qbsP] a_times_x'_def)
  also have "... = \<P>(f in a_times_x. f 1 \<ge> 1) / \<P>(f in a_times_x. f 1 \<ge> 0)"
    by(auto simp add: cond_prob_def) (meson dual_order.trans linordered_nonzero_semiring_class.zero_le_one)
  also have "... = 1 / 2"
  proof -
    have [simp]: "{-2<..<2::real} \<inter> Collect ((\<le>) 1) = {1..<2}" "{-2<..<2::real} \<inter> Collect ((\<le>) 0) = {0..<2}"
      by auto
    show ?thesis
      by(auto simp: prob_a_times_x)
  qed
  finally show ?thesis .
qed


text \<open> Almost everywhere, integrable, and integrations are also interpreted as programs.\<close>
lemma "(\<lambda>g f x. if (AE\<^sub>Q y in g x. f x y \<noteq> \<infinity>) then (\<integral>\<^sup>+\<^sub>Q y. f x y \<partial>(g x)) else 0)
        \<in> (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  by simp

lemma "(\<lambda>g f x. if qbs_integrable (g x) (f x) then Some (\<integral>\<^sub>Q y. f x y \<partial>(g x)) else None)
        \<in> (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q option_qbs \<real>\<^sub>Q"
  by simp

end