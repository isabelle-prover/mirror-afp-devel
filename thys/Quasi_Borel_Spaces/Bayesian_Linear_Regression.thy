(*  Title:   Bayesian_Linear_Regression.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open> Bayesian Linear Regression \<close>

theory Bayesian_Linear_Regression
  imports "Measure_as_QuasiBorel_Measure"
begin

text \<open> We formalize the Bayesian linear regression presented in \<^cite>\<open>"Heunen_2017"\<close> section VI.\<close>
subsubsection \<open> Prior \<close>
abbreviation "\<nu> \<equiv> density lborel (\<lambda>x. ennreal (normal_density 0 3 x))"

interpretation \<nu>: standard_borel_prob_space \<nu>
  by(simp add: standard_borel_prob_space_def prob_space_normal_density)

term "\<nu>.as_qbs_measure :: real qbs_prob_space"
definition prior :: "(real \<Rightarrow> real) qbs_prob_space" where
 "prior \<equiv> do { s \<leftarrow> \<nu>.as_qbs_measure ;
                b \<leftarrow> \<nu>.as_qbs_measure ;
                qbs_return (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) (\<lambda>r. s * r + b)}"

lemma \<nu>_as_qbs_measure_eq:
 "\<nu>.as_qbs_measure = qbs_prob_space (\<real>\<^sub>Q,id,\<nu>)"
  by(simp add: \<nu>.as_qbs_measure_retract[of id id] distr_id' measure_to_qbs_cong_sets[OF sets_density] measure_to_qbs_cong_sets[OF sets_lborel])

interpretation \<nu>_qp: pair_qbs_prob "\<real>\<^sub>Q" id \<nu> "\<real>\<^sub>Q" id \<nu>
  by(auto intro!: qbs_probI prob_space_normal_density simp: pair_qbs_prob_def)

lemma \<nu>_as_qbs_measure_in_Pr:
 "\<nu>.as_qbs_measure \<in> monadP_qbs_Px \<real>\<^sub>Q"
  by(simp add: \<nu>_as_qbs_measure_eq \<nu>_qp.qp1.qbs_prob_space_in_Px)

lemma sets_real_real_real[measurable_cong]:
  "sets (qbs_to_measure ((\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q)) = sets ((borel \<Otimes>\<^sub>M borel) \<Otimes>\<^sub>M borel)"
  by (metis pair_standard_borel.l_r_r_sets pair_standard_borel_def r_preserves_product real.standard_borel_axioms real_real.standard_borel_axioms)

lemma lin_morphism:
 "(\<lambda>(s, b) r. s * r + b) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q"
  apply(simp add: split_beta')
  apply(rule curry_preserves_morphisms[of "\<lambda>(x,r). fst x * r + snd x",simplified curry_def split_beta',simplified])
  by auto

lemma lin_measurable[measurable]:
 "(\<lambda>(s, b) r. s * r + b) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M qbs_to_measure (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q)"
  using lin_morphism l_preserves_morphisms[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q" "exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q"]
  by auto

lemma prior_computation:
 "qbs_prob (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) ((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)" 
 "prior = qbs_prob_space (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q, (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g, distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
  using \<nu>_qp.qbs_bind_bind_return[OF lin_morphism]
  by(simp_all add: prior_def \<nu>_as_qbs_measure_eq map_prod_def)

text \<open> The following lemma corresponds to the equation (5). \<close>
lemma prior_measure:
  "qbs_prob_measure prior = distr (\<nu> \<Otimes>\<^sub>M \<nu>) (qbs_to_measure (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)) (\<lambda>(s,b) r. s * r + b)"
  by(simp add: prior_computation(2) qbs_prob.qbs_prob_measure_computation[OF prior_computation(1)])    (simp add: distr_distr comp_def)

lemma prior_in_space:
 "prior \<in> qbs_space (monadP_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q))"
  using qbs_prob.qbs_prob_space_in_Px[OF prior_computation(1)]
  by(simp add: prior_computation(2))


subsubsection \<open> Likelihood \<close>
abbreviation "d \<mu> x \<equiv> normal_density \<mu> (1/2) x"

lemma d_positive : "0 < d \<mu> x"
  by(simp add: normal_density_pos)

definition obs :: "(real \<Rightarrow> real) \<Rightarrow> ennreal" where
"obs f \<equiv> d (f 1) 2.5 * d (f 2) 3.8 * d (f 3) 4.5 * d (f 4) 6.2 * d (f 5) 8"

lemma obs_morphism:
 "obs \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q)"
  then have [measurable]:"(\<lambda>(x,y). \<alpha> x y) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M real_borel"
    by(auto simp: exp_qbs_Mx_def)
  show "obs \<circ> \<alpha> \<in> qbs_Mx \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    by(auto simp: comp_def obs_def normal_density_def)
qed

lemma obs_measurable[measurable]:
 "obs \<in> qbs_to_measure (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q) \<rightarrow>\<^sub>M ennreal_borel"
  using obs_morphism by auto


subsubsection \<open> Posterior \<close>
lemma id_obs_morphism:
 "(\<lambda>f. (f,obs f)) \<in> \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  by(rule qbs_morphism_tuple[OF qbs_morphism_ident' obs_morphism])

lemma push_forward_measure_in_space:
 "monadP_qbs_Pf (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) (\<lambda>f. (f,obs f)) prior \<in> qbs_space (monadP_qbs ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0))"
  by(rule qbs_morphismE(2)[OF monadP_qbs_Pf_morphism[OF id_obs_morphism] prior_in_space])

lemma push_forward_measure_computation:
 "qbs_prob ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) (\<lambda>l. (((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) l, ((obs \<circ> (\<lambda>(s, b) r. s * r + b)) \<circ> real_real.g) l)) (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
 "monadP_qbs_Pf (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) (\<lambda>f. (f, obs f)) prior = qbs_prob_space ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0, (\<lambda>l. (((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) l, ((obs \<circ> (\<lambda>(s, b) r. s * r + b)) \<circ> real_real.g) l)), distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
  using qbs_prob.monadP_qbs_Pf_computation[OF prior_computation id_obs_morphism] by(auto simp: comp_def)

subsubsection \<open> Normalizer \<close>
text \<open> We use the unit space for an error. \<close>
definition norm_qbs_measure :: "('a \<times> ennreal) qbs_prob_space \<Rightarrow> 'a qbs_prob_space + unit" where
"norm_qbs_measure p \<equiv> (let (XR,\<alpha>\<beta>,\<nu>) = rep_qbs_prob_space p in
                          if emeasure (density \<nu> (snd \<circ> \<alpha>\<beta>)) UNIV = 0 then Inr ()
                          else if emeasure (density \<nu> (snd \<circ> \<alpha>\<beta>)) UNIV = \<infinity> then Inr ()
                          else Inl (qbs_prob_space (map_qbs fst XR, fst \<circ> \<alpha>\<beta>, density \<nu> (\<lambda>r. snd (\<alpha>\<beta> r) / emeasure (density \<nu> (snd \<circ> \<alpha>\<beta>)) UNIV))))"


lemma norm_qbs_measure_qbs_prob:
  assumes "qbs_prob (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) (\<lambda>r. (\<alpha> r, \<beta> r)) \<mu>"
          "emeasure (density \<mu> \<beta>) UNIV \<noteq> 0"
      and "emeasure (density \<mu> \<beta>) UNIV \<noteq> \<infinity>"
    shows "qbs_prob X \<alpha> (density \<mu> (\<lambda>r. (\<beta> r) / emeasure (density \<mu> \<beta>) UNIV))"
proof -
  interpret qp: qbs_prob "X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" "\<lambda>r. (\<alpha> r, \<beta> r)" \<mu>
    by fact
  have ha[simp]: "\<alpha> \<in> qbs_Mx X"
   and hb[measurable] :"\<beta> \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
    using assms by(simp_all add: qbs_prob_def in_Mx_def pair_qbs_Mx_def comp_def)
  show ?thesis
  proof(rule qbs_probI)
    show "prob_space (density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV))"
    proof(rule prob_spaceI)
      show "emeasure (density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV)) (space (density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV))) = 1"
             (is "?lhs = ?rhs")
      proof -
        have "?lhs = emeasure (density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV)) UNIV"
          by simp
        also have "... = (\<integral>\<^sup>+r\<in>UNIV. (\<beta> r / emeasure (density \<mu> \<beta>) UNIV) \<partial>\<mu>)"
          by(intro emeasure_density) auto
        also have "... =  integral\<^sup>N \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV)"
          by simp
        also have "... = (integral\<^sup>N \<mu> \<beta>) / emeasure (density \<mu> \<beta>) UNIV"
          by(simp add: nn_integral_divide)
        also have "... = (\<integral>\<^sup>+r\<in>UNIV. \<beta> r \<partial>\<mu>) / emeasure (density \<mu> \<beta>) UNIV"
          by(simp add: emeasure_density)
        also have "... = 1"
          using assms(2,3) by(simp add: emeasure_density divide_eq_1_ennreal)
        finally show ?thesis .
      qed
    qed
  qed simp_all
qed

lemma norm_qbs_measure_computation:
  assumes "qbs_prob (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) (\<lambda>r. (\<alpha> r, \<beta> r)) \<mu>"
  shows "norm_qbs_measure (qbs_prob_space (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0, (\<lambda>r. (\<alpha> r, \<beta> r)), \<mu>)) = (if emeasure (density \<mu> \<beta>) UNIV = 0 then Inr ()
                                                                                else if emeasure (density \<mu> \<beta>) UNIV = \<infinity> then Inr ()
                                                                                else Inl (qbs_prob_space (X, \<alpha>, density \<mu> (\<lambda>r. (\<beta> r) / emeasure (density \<mu> \<beta>) UNIV))))"
proof -
  interpret qp: qbs_prob "X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" "\<lambda>r. (\<alpha> r, \<beta> r)" \<mu>
    by fact
  have ha: "\<alpha> \<in> qbs_Mx X"
   and hb[measurable] :"\<beta> \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
    using assms by(simp_all add: qbs_prob_def in_Mx_def pair_qbs_Mx_def comp_def)
  show ?thesis
    unfolding norm_qbs_measure_def
  proof(rule qp.in_Rep_induct)
    fix XR \<alpha>\<beta>' \<mu>'
    assume "(XR,\<alpha>\<beta>',\<mu>') \<in> Rep_qbs_prob_space (qbs_prob_space (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0, \<lambda>r. (\<alpha> r, \<beta> r), \<mu>))"
    from qp.if_in_Rep[OF this]
    have h:"XR = X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
           "qbs_prob XR \<alpha>\<beta>' \<mu>'"
           "qbs_prob_eq (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0, \<lambda>r. (\<alpha> r, \<beta> r), \<mu>) (XR, \<alpha>\<beta>', \<mu>')"
      by auto
    have hint: "\<And>f. f \<in> X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<Longrightarrow> (\<integral>\<^sup>+ x. f (\<alpha> x, \<beta> x) \<partial>\<mu>) = (\<integral>\<^sup>+ x. f (\<alpha>\<beta>' x) \<partial>\<mu>')"
      using h(3)[simplified qbs_prob_eq_equiv14] by(simp add: qbs_prob_eq4_def)
    interpret qp': qbs_prob XR \<alpha>\<beta>' \<mu>'
      by fact
    have ha': "fst \<circ> \<alpha>\<beta>' \<in> qbs_Mx X" "(\<lambda>x. fst (\<alpha>\<beta>' x)) \<in> qbs_Mx X"
     and hb'[measurable]: "snd \<circ> \<alpha>\<beta>' \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel" "(\<lambda>x. snd (\<alpha>\<beta>' x)) \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel" "(\<lambda>x. fst (\<alpha>\<beta>' x)) \<in> real_borel \<rightarrow>\<^sub>M qbs_to_measure X"
      using h by(simp_all add: qbs_prob_def in_Mx_def pair_qbs_Mx_def comp_def)
    have fstX: "map_qbs fst XR = X"
      by(simp add: h(1) pair_qbs_fst)
    have he:"emeasure (density \<mu> \<beta>) UNIV = emeasure (density \<mu>' (snd \<circ> \<alpha>\<beta>')) UNIV"
      using hint[OF snd_qbs_morphism] by(simp add: emeasure_density)

    show "(let a = (XR,\<alpha>\<beta>',\<mu>') in case a of (XR, \<alpha>\<beta>, \<nu>') \<Rightarrow> if emeasure (density \<nu>' (snd \<circ> \<alpha>\<beta>)) UNIV = 0 then Inr ()
                                                else if emeasure (density \<nu>' (snd \<circ> \<alpha>\<beta>)) UNIV = \<infinity> then Inr ()
                                                else Inl (qbs_prob_space (map_qbs fst XR, fst \<circ> \<alpha>\<beta>, density \<nu>' (\<lambda>r. snd (\<alpha>\<beta> r) / emeasure (density \<nu>' (snd \<circ> \<alpha>\<beta>)) UNIV))))
         = (if emeasure (density \<mu> \<beta>) UNIV = 0 then Inr ()
            else if emeasure (density \<mu> \<beta>) UNIV = \<infinity> then Inr ()
            else Inl (qbs_prob_space (X, \<alpha>, density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV))))"
    proof(auto simp: he[symmetric] fstX)
      assume het0:"emeasure (density \<mu> \<beta>) UNIV \<noteq> \<top>"
                  "emeasure (density \<mu> \<beta>) UNIV \<noteq> 0"
      interpret pqp: pair_qbs_prob X "fst \<circ> \<alpha>\<beta>'" "density \<mu>' (\<lambda>r. snd (\<alpha>\<beta>' r) / emeasure (density \<mu> \<beta>) UNIV)" X \<alpha> "density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV)"
        apply(auto intro!: norm_qbs_measure_qbs_prob  simp: pair_qbs_prob_def assms het0)
        using het0
        by(auto intro!: norm_qbs_measure_qbs_prob[of X "fst \<circ> \<alpha>\<beta>'" "snd \<circ> \<alpha>\<beta>'",simplified,OF h(2)[simplified h(1)]] simp: he)

      show "qbs_prob_space (X, fst \<circ> \<alpha>\<beta>', density \<mu>' (\<lambda>r. snd (\<alpha>\<beta>' r) / emeasure (density \<mu> \<beta>) UNIV)) = qbs_prob_space (X, \<alpha>, density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV))"
      proof(rule pqp.qbs_prob_space_eq4)
        fix f
        assume hf[measurable]:"f \<in> qbs_to_measure X \<rightarrow>\<^sub>M ennreal_borel"
        show "(\<integral>\<^sup>+ x. f ((fst \<circ> \<alpha>\<beta>') x) \<partial>density \<mu>' (\<lambda>r. snd (\<alpha>\<beta>' r) / emeasure (density \<mu> \<beta>) UNIV)) = (\<integral>\<^sup>+ x. f (\<alpha> x) \<partial>density \<mu> (\<lambda>r. \<beta> r / emeasure (density \<mu> \<beta>) UNIV))"
             (is "?lhs = ?rhs")
        proof -
          have "?lhs =  (\<integral>\<^sup>+ x. (\<lambda>xr. (snd xr) / emeasure (density \<mu> \<beta>) UNIV * f (fst xr)) (\<alpha>\<beta>' x) \<partial>\<mu>')"
            by(auto simp: nn_integral_density)
          also have "... = (\<integral>\<^sup>+ x. (\<lambda>xr. (snd xr) / emeasure (density \<mu> \<beta>) UNIV * f (fst xr)) (\<alpha> x,\<beta> x) \<partial>\<mu>)"
            by(intro hint[symmetric]) (auto intro!: pair_qbs_morphismI)
          also have "... = ?rhs"
            by(simp add: nn_integral_density)
          finally show ?thesis .
        qed
      qed simp
    qed
  qed
qed

lemma norm_qbs_measure_morphism:
 "norm_qbs_measure \<in> monadP_qbs (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) \<rightarrow>\<^sub>Q monadP_qbs X <+>\<^sub>Q 1\<^sub>Q"
proof(rule qbs_morphismI)
  fix \<gamma>
  assume "\<gamma> \<in> qbs_Mx (monadP_qbs (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0))"
  then obtain \<alpha> g where hc:
   "\<alpha> \<in> qbs_Mx (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0)" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      "\<gamma> = (\<lambda>r. qbs_prob_space (X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0, \<alpha>, g r))"
    using rep_monadP_qbs_MPx[of "\<gamma>" "(X \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0)"] by auto
  note [measurable] = hc(2) measurable_prob_algebraD[OF hc(2)]
  have setsg[measurable_cong]:"\<And>r. sets (g r) = sets real_borel"
    using measurable_space[OF hc(2)] by(simp add: space_prob_algebra)
  then have ha: "fst \<circ> \<alpha> \<in> qbs_Mx X"
   and hb[measurable]: "snd \<circ> \<alpha> \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel" "(\<lambda>x. snd (\<alpha> x)) \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel" "\<And>r. snd \<circ> \<alpha> \<in> g r  \<rightarrow>\<^sub>M ennreal_borel" "\<And>r. (\<lambda>x. snd (\<alpha> x)) \<in> g r  \<rightarrow>\<^sub>M ennreal_borel"
    using hc(1) by(auto simp add: pair_qbs_Mx_def measurable_cong_sets[OF setsg refl] comp_def)
  have emeas_den_meas[measurable]: "\<And>U. U \<in> sets real_borel \<Longrightarrow> (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) U) \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
    by(simp add: emeasure_density)
  have S_setsc:"UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0,\<infinity>} \<in> sets real_borel"
    using measurable_sets_borel[OF emeas_den_meas] by simp
  have space_non_empty:"qbs_space (monadP_qbs X) \<noteq> {}"
    using ha qbs_empty_equiv monadP_qbs_empty_iff[of X] by auto
  have g_meas:"(\<lambda>r. if r \<in> (UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0,\<infinity>}) then density (g r) (\<lambda>l. ((snd \<circ> \<alpha>) l) / emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) else return real_borel 0) \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
  proof -
    have H:"\<And>\<Omega> M N c f. \<Omega> \<inter> space M \<in> sets M \<Longrightarrow> c \<in> space N \<Longrightarrow>
             f \<in> measurable (restrict_space M \<Omega>) N \<Longrightarrow> (\<lambda>x. if x \<in> \<Omega> then f x else c) \<in> measurable M N"
      by(simp add: measurable_restrict_space_iff)
    show ?thesis
    proof(rule H)
      show "(UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0, \<infinity>}) \<inter> space real_borel \<in> sets real_borel"
        using S_setsc by simp
    next
      show "(\<lambda>r. density (g r) (\<lambda>l. ((snd \<circ> \<alpha>) l) / emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV)) \<in> restrict_space real_borel (UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0,\<infinity>}) \<rightarrow>\<^sub>M prob_algebra real_borel"
      proof(rule measurable_prob_algebra_generated[where \<Omega>=UNIV and G="sets real_borel"])

        fix a
        assume "a \<in> space (restrict_space real_borel (UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0, \<infinity>}))"
        then have 1:"(\<integral>\<^sup>+ x. snd (\<alpha> x) \<partial>g a) \<noteq> 0" "(\<integral>\<^sup>+ x. snd (\<alpha> x) \<partial>g a) \<noteq> \<infinity>"
          by(simp_all add: space_restrict_space emeasure_density)
        show "prob_space (density (g a) (\<lambda>l. (snd \<circ> \<alpha>) l / emeasure (density (g a) (snd \<circ> \<alpha>)) UNIV))"
          using 1
          by(auto intro!: prob_spaceI simp: emeasure_density nn_integral_divide divide_eq_1_ennreal)
      next
        fix U
        assume 1:"U \<in> sets real_borel"
        then have 2:"\<And>a. U \<in> sets (g a)" by auto
        show "(\<lambda>a. emeasure (density (g a) (\<lambda>l. (snd \<circ> \<alpha>) l / emeasure (density (g a) (snd \<circ> \<alpha>)) UNIV)) U) \<in> (restrict_space real_borel (UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0, \<infinity>})) \<rightarrow>\<^sub>M ennreal_borel"
          using 1
          by(auto intro!: measurable_restrict_space1 nn_integral_measurable_subprob_algebra2[where N=real_borel] simp: emeasure_density emeasure_density[OF _ 2])
      qed (simp_all add: setsg sets.Int_stable sets.sigma_sets_eq[of real_borel,simplified])
    qed (simp add:space_prob_algebra prob_space_return)
  qed

  show "norm_qbs_measure \<circ> \<gamma> \<in> qbs_Mx (monadP_qbs X <+>\<^sub>Q unit_quasi_borel)"
    apply(auto intro!: bexI[OF _ S_setsc] bexI[where x="(\<lambda>r. ())"] bexI[where x="\<lambda>r. qbs_prob_space (X,fst \<circ> \<alpha>,if r \<in> (UNIV - (\<lambda>r. emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) -` {0,\<infinity>}) then density (g r) (\<lambda>l. ((snd \<circ> \<alpha>) l) / emeasure (density (g r) (snd \<circ> \<alpha>)) UNIV) else return real_borel 0)"]
                 simp: copair_qbs_Mx_equiv copair_qbs_Mx2_def space_non_empty[simplified])
     apply standard
     apply(simp add: hc(3) norm_qbs_measure_computation[of _ "fst \<circ> \<alpha>" "snd \<circ> \<alpha>",simplified,OF qbs_prob_MPx[OF hc(1,2)]])
    apply(simp add: monadP_qbs_MPx_def in_MPx_def)
    apply(auto intro!: bexI[OF _ ha] bexI[OF _ g_meas])
    done
qed


text \<open> The following is the semantics of the entire program. \<close>
definition program :: "(real \<Rightarrow> real) qbs_prob_space + unit" where
 "program \<equiv> norm_qbs_measure (monadP_qbs_Pf (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) ((\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Otimes>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0) (\<lambda>f. (f,obs f)) prior)"

lemma program_in_space:
 "program \<in> qbs_space (monadP_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) <+>\<^sub>Q 1\<^sub>Q)"
  unfolding program_def
  by(rule qbs_morphismE(2)[OF norm_qbs_measure_morphism push_forward_measure_in_space])


text \<open> We calculate the normalizing constant. \<close>
lemma complete_the_square:
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  shows "a*x\<^sup>2 + b * x + c = a * (x + (b / (2*a)))\<^sup>2 - ((b\<^sup>2 - 4* a * c)/(4*a))"
  using assms by(simp add: comm_semiring_1_class.power2_sum power2_eq_square[of "b / (2 * a)"] ring_class.ring_distribs(1) division_ring_class.diff_divide_distrib power2_eq_square[of b])

lemma complete_the_square2':
  fixes a b c x :: real
  assumes "a \<noteq> 0"
  shows "a*x\<^sup>2 - 2 * b * x + c = a * (x - (b / a))\<^sup>2 - ((b\<^sup>2 - a*c)/a)"
  using complete_the_square[OF assms,where b="-2 * b" and x=x and c=c]
  by(simp add: division_ring_class.diff_divide_distrib assms)


lemma normal_density_mu_x_swap:
   "normal_density \<mu> \<sigma> x = normal_density x \<sigma> \<mu>"
  by(simp add: normal_density_def power2_commute)

lemma normal_density_plus_shift:
 "normal_density \<mu> \<sigma> (x + y) = normal_density (\<mu> - x) \<sigma> y"
  by(simp add: normal_density_def add.commute diff_diff_eq2)

lemma normal_density_times:
  assumes "\<sigma> > 0" "\<sigma>' > 0"
  shows "normal_density \<mu> \<sigma> x * normal_density \<mu>' \<sigma>' x = (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) * exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) * normal_density ((\<mu>*\<sigma>'\<^sup>2 + \<mu>'*\<sigma>\<^sup>2)/(\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x"
        (is "?lhs = ?rhs")
proof -
  have non0: "2*\<sigma>\<^sup>2 \<noteq> 0" "2*\<sigma>'\<^sup>2 \<noteq> 0" "\<sigma>\<^sup>2 + \<sigma>'\<^sup>2 \<noteq> 0"
    using assms by auto
  have "?lhs = exp (- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2))) * exp (- ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2)) "
    by(simp add: normal_density_def)
  also have "... = exp (- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2)) - ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2))"
    by(simp add: exp_add[of "- ((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2))" "- ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2))",simplified add_uminus_conv_diff])
  also have "... = exp (- (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) - (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))  / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2))"
  proof -
    have "((x - \<mu>)\<^sup>2 / (2 * \<sigma>\<^sup>2)) + ((x - \<mu>')\<^sup>2 / (2 * \<sigma>'\<^sup>2)) = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) + (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))"
         (is "?lhs' = ?rhs'")
    proof -
      have "?lhs' = (2 * ((x - \<mu>)\<^sup>2 * \<sigma>'\<^sup>2) + 2 * ((x - \<mu>')\<^sup>2 * \<sigma>\<^sup>2)) / (4 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: field_class.add_frac_eq[OF non0(1,2)])
      also have "... = ((x - \<mu>)\<^sup>2 * \<sigma>'\<^sup>2 + (x - \<mu>')\<^sup>2 * \<sigma>\<^sup>2) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: power2_eq_square division_ring_class.add_divide_distrib)
      also have "... = ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * x\<^sup>2 - 2 * (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) * x  + (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: comm_ring_1_class.power2_diff ring_class.left_diff_distrib semiring_class.distrib_right)
       also have "... = ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 - ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)\<^sup>2 - (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp only: complete_the_square2'[OF non0(3),of x "(\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)" "(\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)"])
      also have "... = ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)) - (((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)\<^sup>2 - (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: division_ring_class.diff_divide_distrib)
      also have "... = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * ((\<sigma> * \<sigma>') / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) - (((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2)\<^sup>2 - (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2)) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) / (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2))"
        by(simp add: monoid_mult_class.power2_eq_square[of "(\<sigma> * \<sigma>') / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)"] ab_semigroup_mult_class.mult.commute[of "\<sigma>\<^sup>2 + \<sigma>'\<^sup>2"] )
          (simp add: monoid_mult_class.power2_eq_square[of \<sigma>] monoid_mult_class.power2_eq_square[of \<sigma>'])
      also have "... =  (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) - ((\<mu> * \<sigma>'\<^sup>2)\<^sup>2 + (\<mu>' * \<sigma>\<^sup>2)\<^sup>2 + 2 * (\<mu> * \<sigma>'\<^sup>2) * (\<mu>' * \<sigma>\<^sup>2) - (\<sigma>\<^sup>2 * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2) + \<sigma>\<^sup>2 * (\<mu>\<^sup>2 * \<sigma>'\<^sup>2) + (\<sigma>'\<^sup>2 * (\<mu>'\<^sup>2 * \<sigma>\<^sup>2) + \<sigma>'\<^sup>2 * (\<mu>\<^sup>2 * \<sigma>'\<^sup>2)))) / ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)))"
        by(simp add: comm_semiring_1_class.power2_sum[of "\<mu> * \<sigma>'\<^sup>2" "\<mu>' * \<sigma>\<^sup>2"] semiring_class.distrib_right[of "\<sigma>\<^sup>2" "\<sigma>'\<^sup>2" "\<mu>'\<^sup>2 * \<sigma>\<^sup>2 + \<mu>\<^sup>2 * \<sigma>'\<^sup>2"] )
          (simp add: semiring_class.distrib_left[of _ "\<mu>'\<^sup>2 * \<sigma>\<^sup>2 " "\<mu>\<^sup>2 * \<sigma>'\<^sup>2"])
      also have "... = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) + ((\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)*\<mu>\<^sup>2 + (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)*\<mu>'\<^sup>2 - (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2) * 2 * (\<mu>*\<mu>')) / ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * (2 * (\<sigma>\<^sup>2 * \<sigma>'\<^sup>2)))"
        by(simp add: monoid_mult_class.power2_eq_square division_ring_class.minus_divide_left)
      also have "... = (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) + (\<mu>\<^sup>2 + \<mu>'\<^sup>2 - 2 * (\<mu>*\<mu>')) / ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) * 2)"
        using assms by(simp add: division_ring_class.add_divide_distrib division_ring_class.diff_divide_distrib)
      also have "... = ?rhs'"
        by(simp add: comm_ring_1_class.power2_diff ab_semigroup_mult_class.mult.commute[of 2])
      finally show ?thesis .
    qed
    thus ?thesis
      by simp
  qed
  also have "... = (exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2))) * sqrt (2 * pi * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2)  * normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x"
    by(simp add: exp_add[of "- (x - (\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2 / (2 * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2)" "- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))",simplified] normal_density_def)
  also have "... = ?rhs" 
  proof -
    have "exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) / (sqrt (2 * pi * \<sigma>\<^sup>2) * sqrt (2 * pi * \<sigma>'\<^sup>2)) * sqrt (2 * pi * (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))\<^sup>2) = 1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))"
      using assms by(simp add: real_sqrt_mult)
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma normal_density_times':
  assumes "\<sigma> > 0" "\<sigma>' > 0"
  shows "a * normal_density \<mu> \<sigma> x * normal_density \<mu>' \<sigma>' x = a * (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) * exp (- (\<mu> - \<mu>')\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) * normal_density ((\<mu>*\<sigma>'\<^sup>2 + \<mu>'*\<sigma>\<^sup>2)/(\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x"
  using normal_density_times[OF assms,of \<mu> x \<mu>']
  by (simp add: mult.assoc)

lemma normal_density_times_minusx:
  assumes "\<sigma> > 0" "\<sigma>' > 0" "a \<noteq> a'"
  shows "normal_density (\<mu> - a*x) \<sigma> y * normal_density (\<mu>' - a'*x) \<sigma>' y = (1 / \<bar>a' - a\<bar>) * normal_density ((\<mu>'- \<mu>)/(a'-a)) (sqrt ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)/(a' - a)\<^sup>2)) x * normal_density (((\<mu> - a*x)*\<sigma>'\<^sup>2 + (\<mu>' - a'*x)*\<sigma>\<^sup>2)/(\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) y"
proof -
  have non0:"a' - a \<noteq> 0"
    using assms(3) by simp
  have "1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- (\<mu> - a * x - (\<mu>' - a' * x))\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2))) = 1 / \<bar>a' - a\<bar> * normal_density ((\<mu>' - \<mu>) / (a' - a)) (sqrt ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) / (a' - a)\<^sup>2)) x"
       (is "?lhs = ?rhs")
  proof -
    have "?lhs = 1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- ((a' - a) * x - (\<mu>' - \<mu>))\<^sup>2 / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))"
      by(simp add: ring_class.left_diff_distrib group_add_class.diff_diff_eq2 add.commute add_diff_eq)
    also have "... = 1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- ((a' - a)\<^sup>2 * (x - (\<mu>' - \<mu>)/(a' - a))\<^sup>2) / (2 * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))"
    proof -
      have "((a' - a) * x - (\<mu>' - \<mu>))\<^sup>2 = ((a' - a) * (x - (\<mu>' - \<mu>)/(a' - a)))\<^sup>2"
        using non0 by(simp add: ring_class.right_diff_distrib[of "a'-a" x])
      also have "... = (a' - a)\<^sup>2 * (x - (\<mu>' - \<mu>)/(a' - a))\<^sup>2"
        by(simp add: monoid_mult_class.power2_eq_square)
      finally show ?thesis
        by simp
    qed
    also have "... = 1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * sqrt (2 * pi * (sqrt ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)/(a' - a)\<^sup>2))\<^sup>2) * normal_density ((\<mu>' - \<mu>) / (a' - a)) (sqrt ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) / (a' - a)\<^sup>2)) x"
      using non0 by (simp add: normal_density_def)
    also have "... = ?rhs"
    proof -
      have "1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * sqrt (2 * pi * (sqrt ((\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)/(a' - a)\<^sup>2))\<^sup>2) = 1 / \<bar>a' - a\<bar>"
        using assms by(simp add: real_sqrt_divide[symmetric]) (simp add: real_sqrt_divide)
      thus ?thesis
        by simp
    qed
    finally show ?thesis .
  qed
  thus ?thesis
    by(simp add:normal_density_times[OF assms(1,2),of "\<mu> - a*x" y "\<mu>' - a'*x"])
qed

text \<open> The following is the normalizing constant of the program. \<close>
abbreviation "C \<equiv> ennreal ((4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))) * (exp (- (1674761 / 1674025))))"

lemma program_normalizing_constant:
 "emeasure (density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g)) UNIV = C"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+ x. (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) x \<partial> (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f))"
    by(simp add: emeasure_density)
  also have "... = (\<integral>\<^sup>+ z. (obs \<circ> (\<lambda>(s, b) r. s * r + b)) z \<partial>(\<nu> \<Otimes>\<^sub>M \<nu>))"
    using nn_integral_distr[of real_real.f "\<nu> \<Otimes>\<^sub>M \<nu>" real_borel "obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g",simplified]
    by(simp add: comp_def)
  also have "... = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. (obs \<circ> (\<lambda>(s, b) r. s * r + b)) (x, y) \<partial>\<nu> \<partial>\<nu>)"
    by(simp only: \<nu>_qp.nn_integral_snd[where f="(obs \<circ> (\<lambda>(s, b) r. s * r + b))",simplified,symmetric])
      (simp add: \<nu>_qp.Fubini[where f="(obs \<circ> (\<lambda>(s, b) r. s * r + b))",simplified])
  also have "... = (\<integral>\<^sup>+ x. 2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x \<partial>\<nu>)"
  proof(rule nn_integral_cong[where M=\<nu>,simplified])
    fix x
    have [measurable]: "(\<lambda>y. obs (\<lambda>r. x * r + y)) \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
      using measurable_Pair2[of "obs \<circ> (\<lambda>(s, b) r. s * r + b)"] by auto
    show "(\<integral>\<^sup>+ y. (obs \<circ> (\<lambda>(s, b) r. s * r + b)) (x, y) \<partial>\<nu>) = 2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x"
          (is "?lhs' = ?rhs'")
    proof -
      have "?lhs' = (\<integral>\<^sup>+ y. ennreal (d (5 / 2 - x) y * d (19 / 5 - x * 2) y * d (9 / 2 - x * 3) y * d (31 / 5 - x * 4) y * d (8 - x * 5) y * normal_density 0 3 y) \<partial>lborel)"
        by(simp add: nn_integral_density obs_def normal_density_mu_x_swap[where x="5/2"] normal_density_mu_x_swap[where x="19/5"] normal_density_mu_x_swap[where x="9/2"] normal_density_mu_x_swap[where x="31/5"] normal_density_mu_x_swap[where x="8"] normal_density_plus_shift ab_semigroup_mult_class.mult.commute[of "ennreal (normal_density 0 3 _)"] ennreal_mult'[symmetric])
      also have "... = (\<integral>\<^sup>+ y. ennreal (2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density (20 / 181 * 9 * (5 - 3 * x)) (3 / (2 * sqrt 5) / sqrt (181 / 20)) y) \<partial>lborel)"
      proof(rule nn_integral_cong[where M=lborel,simplified])
        fix y
        have "d (5 / 2 - x) y * d (19 / 5 - x * 2) y * d (9 / 2 - x * 3) y * d (31 / 5 - x * 4) y * d (8 - x * 5) y * normal_density 0 3 y = 2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density (20 / 181 * 9 * (5 - 3 * x)) (3 / (2 * sqrt 5) / sqrt (181 / 20)) y"
             (is "?lhs'' = ?rhs''")
        proof -
          have "?lhs'' = normal_density (13 / 10) (1 / sqrt 2) x * normal_density (63 / 20 - (3 / 2) * x)  (sqrt 2 / 4) y * d (9 / 2 - x * 3) y * d (31 / 5 - x * 4) y * d (8 - x * 5) y * normal_density 0 3 y"
          proof -
            have "d (5 / 2 - x) y * d (19 / 5 - x * 2) y = normal_density (13 / 10) (1 / sqrt 2) x * normal_density (63 / 20 - (3 / 2) * x) (sqrt 2 / 4) y"
              by(simp add: normal_density_times_minusx[of "1/2" "1/2" 1 2 "5/2" x y "19/5",simplified ab_semigroup_mult_class.mult.commute[of 2 x],simplified])
                (simp add: monoid_mult_class.power2_eq_square real_sqrt_divide division_ring_class.diff_divide_distrib)
            thus ?thesis
              by simp
          qed
          also have "... = normal_density (13 / 10) (1 / sqrt 2) x * (2 / 3) * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (18 / 5 - 2 * x) (1 / (2 * sqrt 3)) y * d (31 / 5 - x * 4) y * d (8 - x * 5) y * normal_density 0 3 y"
          proof -
            have 1:"sqrt 2 * sqrt 8 / (8 * sqrt 3) = 1 / (2 * sqrt 3)"
              by(simp add: real_sqrt_divide[symmetric] real_sqrt_mult[symmetric])
            have "normal_density (63 / 20 - 3 / 2 * x) (sqrt 2 / 4) y * d (9 / 2 - x * 3) y = (2 / 3) * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (18 / 5 - 2 * x) (1 / (2 * sqrt 3)) y"
              by(simp add: normal_density_times_minusx[of "sqrt 2 / 4" "1 / 2" "3 / 2" 3 "63 / 20" x y "9 / 2",simplified ab_semigroup_mult_class.mult.commute[of 3 x],simplified])
                (simp add: monoid_mult_class.power2_eq_square real_sqrt_divide division_ring_class.diff_divide_distrib 1)
            thus ?thesis
              by simp
          qed
          also have "... = normal_density (13 / 10) (1 / sqrt 2) x * (2 / 3) * normal_density (9 / 10) (1 / sqrt 6) x * (1 / 2) * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (17 / 4 - (5 / 2) * x) (1 / 4) y * d (8 - x * 5) y * normal_density 0 3 y"
          proof -
            have 1:"normal_density (18 / 5 - 2 * x) (1 / (2 * sqrt 3)) y * d (31 / 5 - x * 4) y = (1 / 2) * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (17 / 4 - 5 / 2 * x) (1 / 4) y"
              by(simp add: normal_density_times_minusx[of "1 / (2 * sqrt 3)" "1 / 2" 2 4 "18 / 5" x y "31 / 5",simplified ab_semigroup_mult_class.mult.commute[of 4 x],simplified])
                (simp add: monoid_mult_class.power2_eq_square real_sqrt_divide division_ring_class.diff_divide_distrib)
            show ?thesis
              by(simp add: 1 mult.assoc)
          qed
          also have "... = normal_density (13 / 10) (1 / sqrt 2) x * (2 / 3) * normal_density (9 / 10) (1 / sqrt 6) x * (1 / 2) * normal_density (13 / 10) (1 / sqrt 12) x * (2 / 5) * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 - 3 * x) (1 / (2 * sqrt 5)) y * normal_density 0 3 y"
          proof -
            have 1:"normal_density (17 / 4 - 5 / 2 * x) (1 / 4) y * d (8 - x * 5) y = (2 / 5) * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 - 3 * x) (1 / (2 * sqrt 5)) y"
              by(simp add: normal_density_times_minusx[of "1 / 4" "1 / 2" "5 / 2" 5 "17 / 4" x y 8,simplified ab_semigroup_mult_class.mult.commute[of 5 x],simplified])
                (simp add: monoid_mult_class.power2_eq_square real_sqrt_divide division_ring_class.diff_divide_distrib)
            show ?thesis
              by(simp only: 1 mult.assoc)
          qed
          also have "... = normal_density (13 / 10) (1 / sqrt 2) x * (2 / 3) * normal_density (9 / 10) (1 / sqrt 6) x * (1 / 2) * normal_density (13 / 10) (1 / sqrt 12) x * (2 / 5) * normal_density (3 / 2) (1 / sqrt 20) x * (1 / 3) * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density (20 / 181 * 9 * (5 - 3 * x)) ((3 / (2 * sqrt 5))/ sqrt (181 / 20)) y"
          proof -
            have "normal_density (5 - 3 * x) (1 / (2 * sqrt 5)) y * normal_density 0 3 y = (1 / 3) * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density (20 / 181 * 9 * (5 - 3 * x)) ((3 / (2 * sqrt 5))/ sqrt (181 / 20)) y"
              by(simp add: normal_density_times_minusx[of "1 / (2 * sqrt 5)" 3 3 0 5 x y 0,simplified] monoid_mult_class.power2_eq_square)
            thus ?thesis
              by(simp only: mult.assoc)
          qed
          also have "... = ?rhs''"
            by simp
          finally show ?thesis .
        qed
        thus "ennreal( d (5 / 2 - x) y * d (19 / 5 - x * 2) y * d (9 / 2 - x * 3) y * d (31 / 5 - x * 4) y * d (8 - x * 5) y * normal_density 0 3 y) = ennreal (2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density (20 / 181 * 9 * (5 - 3 * x)) (3 / (2 * sqrt 5) / sqrt (181 / 20)) y )"
          by simp
      qed
      also have "... = (\<integral>\<^sup>+ y. ennreal (normal_density (20 / 181 * 9 * (5 - 3 * x)) (3 / (2 * sqrt 5) / sqrt (181 / 20)) y) * ennreal (2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x) \<partial>lborel)"
        by(simp add: ab_semigroup_mult_class.mult.commute ennreal_mult'[symmetric])
      also have "... = (\<integral>\<^sup>+ y. ennreal (2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x) \<partial> (density lborel (\<lambda>y. ennreal (normal_density (20 / 181 * 9 * (5 - 3 * x)) (3 / (2 * sqrt 5) / sqrt (181 / 20)) y))))"
        by(simp add: nn_integral_density[of "\<lambda>y. ennreal (normal_density (20 / 181 * 9 * (5 - 3 * x)) (3 / (2 * sqrt 5) / sqrt (181 / 20)) y)" lborel,simplified,symmetric])
      also have "... = ?rhs'"
        by(simp add: prob_space.emeasure_space_1[OF prob_space_normal_density[of "3 / (2 * sqrt 5 * sqrt (181 / 20))" "20 / 181 * 9 * (5 - 3 * x)"],simplified])
      finally show ?thesis .
    qed
  qed
  also have "... = (\<integral>\<^sup>+ x. ennreal (2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density 0 3 x) \<partial>lborel)"
    by(simp add: nn_integral_density ab_semigroup_mult_class.mult.commute ennreal_mult'[symmetric])
  also have "... = (\<integral>\<^sup>+ x. (4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))) * exp (- (1674761 / 1674025)) * normal_density (450072 / 334805) (3 * sqrt 181 / sqrt 66961) x \<partial>lborel)"
  proof(rule nn_integral_cong[where M=lborel,simplified])
    fix x
    show "ennreal (2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density 0 3 x) = ennreal ((4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))) * exp (- (1674761 / 1674025)) * normal_density (450072 / 334805) (3 * sqrt 181 / sqrt 66961) x)"
    proof -
      have "2 / 45 * normal_density (13 / 10) (1 / sqrt 2) x * normal_density (9 / 10) (1 / sqrt 6) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density 0 3 x = (4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))) * exp (- (1674761 / 1674025)) * normal_density (450072 / 334805) (3 * sqrt 181 / sqrt 66961) x"
           (is "?lhs' = ?rhs'")
      proof -
        have "?lhs' = 2 / 45 * exp (- (3 / 25)) / sqrt (4 * pi / 3) * normal_density 1 (1 / sqrt 8) x * normal_density (13 / 10) (1 / sqrt 12) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density 0 3 x"
          by(simp add: normal_density_times' monoid_mult_class.power2_eq_square real_sqrt_mult[symmetric])
        also have "... = (2 / (15 * pi * sqrt 5)) * exp (- (42 / 125)) * normal_density (59 / 50) (1 / sqrt 20) x * normal_density (3 / 2) (1 / sqrt 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density 0 3 x"
        proof -
          have 1:"sqrt 8 * sqrt 12 * sqrt (5 / 24) = sqrt 20"
            by(simp add:real_sqrt_mult[symmetric])
          have 2:"sqrt (5 * pi / 12) * (45 * sqrt (4 * pi / 3)) = 15 * (pi * sqrt 5)"
            by(simp add: real_sqrt_mult[symmetric] real_sqrt_divide) (simp add: real_sqrt_mult real_sqrt_mult[of 4 5,simplified])
          have "2 / 45 * exp (- (3 / 25)) / sqrt (4 * pi / 3) * normal_density 1 (1 / sqrt 8) x * normal_density (13 / 10) (1 / sqrt 12) x = (6 / (45 * pi * sqrt 5)) * exp (- (42 / 125)) * normal_density (59 / 50) (1 / sqrt 20) x"
            by(simp add: normal_density_times' monoid_mult_class.power2_eq_square mult_exp_exp[of "- (3 / 25)" "- (27 / 125)",simplified,symmetric] 1 2)
          thus ?thesis
            by simp
        qed
        also have "... = 2 / (15 * pi * sqrt pi) * exp (- (106 / 125)) * normal_density (67 / 50) (sqrt 10 / 20 ) x * normal_density (5 / 3) (sqrt (181 / 180)) x * normal_density 0 3 x"
        proof -
          have "2 / (15 * pi * sqrt 5) * exp (- (42 / 125)) * normal_density (59 / 50) (1 / sqrt 20) x * normal_density (3 / 2) (1 / sqrt 20) x = 2 / (15 * pi * sqrt pi) * exp (- (106 / 125)) * normal_density (67 / 50) (sqrt 10 /20) x"
            by(simp add: normal_density_times' monoid_mult_class.power2_eq_square mult_exp_exp[of "- (42 / 125)" "- (64 / 125)",simplified,symmetric] real_sqrt_divide)
              (simp add: mult.commute)
          thus ?thesis
            by simp
        qed
        also have "... = ((4 * sqrt 5) / (5 * pi\<^sup>2 * sqrt 371)) * exp (- (5961 / 6625)) * normal_density (1786 / 1325) (sqrt 905 / (10 * sqrt 371)) x * normal_density 0 3 x"
        proof -
          have 1:"sqrt (371 * pi / 180) * (15 * pi * sqrt pi) = 5 * pi * pi * sqrt 371 / (2 * sqrt 5)"
            by(simp add: real_sqrt_mult real_sqrt_divide real_sqrt_mult[of 36 5,simplified])
          have 22:"10 = sqrt 5 * 2 * sqrt 5" by simp
          have 2:"sqrt 10 * sqrt (181 / 180) / (20 * sqrt (371 / 360)) = sqrt 905 / (10 * sqrt 371)"
            by(simp add: real_sqrt_mult real_sqrt_divide real_sqrt_mult[of 36 5,simplified] real_sqrt_mult[of 36 10,simplified]  real_sqrt_mult[of 181 5,simplified])
              (simp add: mult.assoc[symmetric] 22)
          have "2 / (15 * pi * sqrt pi) * exp (- (106 / 125)) * normal_density (67 / 50) (sqrt 10 / 20) x * normal_density (5 / 3) (sqrt (181 / 180)) x  = 4 * sqrt 5 / (5 * pi\<^sup>2 * sqrt 371) * exp (- (5961 / 6625)) * normal_density (1786 / 1325) (sqrt 905 / (10 * sqrt 371)) x"
            by(simp add: normal_density_times' monoid_mult_class.power2_eq_square mult_exp_exp[of "- (106 / 125)" "- (343 / 6625)",simplified,symmetric] 1 2)
              (simp add: mult.assoc)
          thus ?thesis
            by simp
        qed
        also have "... = ?rhs'"
        proof -
          have 1: "4 * sqrt 5 / (sqrt (66961 * pi / 3710) * (5 * (pi * pi) * sqrt 371)) = 4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))"
            by(simp add: real_sqrt_mult[of 10 371,simplified] real_sqrt_mult[of 5 2,simplified] real_sqrt_divide monoid_mult_class.power2_eq_square mult.assoc)
              (simp add: mult.assoc[symmetric])
          have 2: "sqrt 905 * 3 / (10 * sqrt 371 * sqrt (66961 / 7420)) = 3 * sqrt 181 / sqrt 66961"
            by(simp add: real_sqrt_mult[of 371 20,simplified] real_sqrt_divide real_sqrt_mult[of 4 5,simplified] real_sqrt_mult[of 181 5,simplified]  mult.commute[of _ 3])
              (simp add: mult.assoc)
          show ?thesis
            by(simp only: 1[symmetric]) (simp add: normal_density_times' monoid_mult_class.power2_eq_square mult_exp_exp[of "- (5961 / 6625)" "- (44657144 / 443616625)",simplified,symmetric] 2)
        qed
        finally show ?thesis .
      qed
      thus ?thesis
        by simp
    qed
  qed
  also have "... = (\<integral>\<^sup>+ x. ennreal (normal_density (450072 / 334805) (3 * sqrt 181 / sqrt 66961) x) *  (ennreal (4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))) * exp (- (1674761 / 1674025))) \<partial>lborel)"
    by(simp add: ab_semigroup_mult_class.mult.commute ennreal_mult'[symmetric])
  also have "... = (\<integral>\<^sup>+ x. (ennreal (4 * sqrt 2 / (pi\<^sup>2 * sqrt (66961 * pi))) * exp (- (1674761 / 1674025))) \<partial>(density lborel (\<lambda>x. ennreal (normal_density (450072 / 334805) (3 * sqrt 181 / sqrt 66961) x))))"
    by(simp add: nn_integral_density[symmetric])
  also have "... = ?rhs"
    by(simp add: prob_space.emeasure_space_1[OF prob_space_normal_density,simplified] ennreal_mult'[symmetric])
  finally show ?thesis .
qed

text \<open> The program returns a probability measure, rather than error. \<close>
lemma program_result:
 "qbs_prob (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) ((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) (density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (\<lambda>r. (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) r / C))"
 "program = Inl (qbs_prob_space (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q, (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g, density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (\<lambda>r. (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) r / C)))"
  using norm_qbs_measure_computation[OF push_forward_measure_computation(1),simplified program_normalizing_constant]
        norm_qbs_measure_qbs_prob[OF push_forward_measure_computation(1),simplified program_normalizing_constant]
  by(simp_all add: push_forward_measure_computation program_def comp_def)

lemma program_inl:
 "program \<in> Inl ` (qbs_space (monadP_qbs (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q)))"
  using program_in_space[simplified program_result(2)]
  by(auto simp: image_def program_result(2))

lemma program_result_measure:
 "qbs_prob_measure (qbs_prob_space (\<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q, (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g, density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (\<lambda>r. (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) r / C)))
   = density (qbs_prob_measure prior) (\<lambda>k. obs k / C)"
 (is "?lhs = ?rhs")
proof -
  interpret qp: qbs_prob "exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q" "(\<lambda>(s, b) r. s * r + b) \<circ> real_real.g" "density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (\<lambda>r. (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) r / C)"
    by(rule  program_result(1))
  have "?lhs = distr (density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (\<lambda>r. obs (((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) r) / C)) (qbs_to_measure (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)) ((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g)"
    using qp.qbs_prob_measure_computation by simp
  also have "... = density (distr (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (qbs_to_measure (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)) ((\<lambda>(s, b) r. s * r + b) \<circ> real_real.g)) (\<lambda>k. obs k / C)"
    by(simp add: density_distr)
  also have "... = ?rhs"
    by(simp add: distr_distr comp_def prior_measure)
  finally show ?thesis .
qed

lemma program_result_measure':
 "qbs_prob_measure (qbs_prob_space (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q, (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g, density (distr (\<nu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (\<lambda>r. (obs \<circ> (\<lambda>(s, b) r. s * r + b) \<circ> real_real.g) r / C)))
   = distr (density (\<nu> \<Otimes>\<^sub>M \<nu>) (\<lambda>(s,b). obs (\<lambda>r. s * r + b) / C)) (qbs_to_measure (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)) (\<lambda>(s, b) r. s * r + b)"
  by(simp only: program_result_measure distr_distr) (simp add: density_distr split_beta' prior_measure)

end