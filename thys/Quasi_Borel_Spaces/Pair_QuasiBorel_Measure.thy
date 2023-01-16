(*  Title:   Pair_QuasiBorel_Measure.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Binary Product Measure\<close>

theory Pair_QuasiBorel_Measure
  imports "Monad_QuasiBorel"
begin

subsubsection \<open> Binary Product Measure\<close>
text \<open> Special case of \<^cite>\<open>"Heunen_2017"\<close> Proposition 23 where $\Omega = \mathbb{R}\times \mathbb{R}$ and $X = X \times Y$.
      Let $[\alpha,\mu ] \in P(X)$ and $[\beta ,\nu] \in P(Y)$. $\alpha\times\beta$ is the $\alpha$ in Proposition 23. \<close>
definition qbs_prob_pair_measure_t :: "['a qbs_prob_t, 'b qbs_prob_t] \<Rightarrow> ('a \<times> 'b) qbs_prob_t" where
"qbs_prob_pair_measure_t p q  \<equiv> (let (X,\<alpha>,\<mu>) = p;
                                     (Y,\<beta>,\<nu>) = q in
                                 (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f))"

lift_definition qbs_prob_pair_measure :: "['a qbs_prob_space, 'b qbs_prob_space] \<Rightarrow> ('a \<times> 'b) qbs_prob_space" (infix "\<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s" 80)
is qbs_prob_pair_measure_t
  unfolding qbs_prob_pair_measure_t_def
proof auto
  fix X X' :: "'a quasi_borel"
  fix Y Y' :: "'b quasi_borel"
  fix \<alpha> \<alpha>' \<mu> \<mu>' \<beta> \<beta>' \<nu> \<nu>'
  assume h:"qbs_prob_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
           "qbs_prob_eq (Y,\<beta>,\<nu>) (Y',\<beta>',\<nu>')"
  then have 1: "X = X'" "Y = Y'"
    by(auto simp: qbs_prob_eq_def)
  interpret pqp1: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_probs_def qbs_prob_eq_dest(1)[OF h(1)] qbs_prob_eq_dest(1)[OF h(2)])
  interpret pqp2: pair_qbs_probs X' \<alpha>' \<mu>' Y' \<beta>' \<nu>'
    by(simp add: pair_qbs_probs_def qbs_prob_eq_dest(2)[OF h(1)] qbs_prob_eq_dest(2)[OF h(2)])
  interpret pqp: pair_qbs_prob "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<beta> \<circ> real_real.g" "distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f" "X' \<Otimes>\<^sub>Q Y'" "map_prod \<alpha>' \<beta>' \<circ> real_real.g" "distr (\<mu>' \<Otimes>\<^sub>M \<nu>') real_borel real_real.f"
    by(auto intro!: qbs_probI pqp1.P.prob_space_distr pqp2.P.prob_space_distr simp: pair_qbs_prob_def)

  show "qbs_prob_eq (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (X' \<Otimes>\<^sub>Q Y', map_prod \<alpha>' \<beta>' \<circ> real_real.g, distr (\<mu>' \<Otimes>\<^sub>M \<nu>') real_borel real_real.f)"
  proof(rule pqp.qbs_prob_space_eq_inverse(1))
    show "qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)
           = qbs_prob_space (X' \<Otimes>\<^sub>Q Y', map_prod \<alpha>' \<beta>' \<circ> real_real.g, distr (\<mu>' \<Otimes>\<^sub>M \<nu>') real_borel real_real.f)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y)))"
        by(simp add: pqp1.qbs_bind_return_pq)
      also have "... = qbs_prob_space (X', \<alpha>', \<mu>') \<bind> (\<lambda>x. qbs_prob_space (Y', \<beta>', \<nu>') \<bind> (\<lambda>y. qbs_return (X' \<Otimes>\<^sub>Q Y') (x, y)))"
        using h by(simp add: qbs_prob_space_eq 1)
      also have "... = ?rhs"
        by(simp add: pqp2.qbs_bind_return_pq)
      finally show ?thesis .
    qed
  qed
qed

lemma(in pair_qbs_probs) qbs_prob_pair_measure_computation:
  "(qbs_prob_space (X,\<alpha>,\<mu>)) \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s (qbs_prob_space (Y,\<beta>,\<nu>)) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g , distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
  "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> real_real.g) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
  by(simp_all add: qbs_prob_pair_measure.abs_eq qbs_prob_pair_measure_t_def qbs_bind_return_pq)

lemma qbs_prob_pair_measure_qbs:
  "qbs_prob_space_qbs (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) = qbs_prob_space_qbs p \<Otimes>\<^sub>Q qbs_prob_space_qbs q"
  by(transfer,simp add: qbs_prob_pair_measure_t_def Let_def prod.case_eq_if)

lemma(in pair_qbs_probs) qbs_prob_pair_measure_measure:
    shows "qbs_prob_measure (qbs_prob_space (X,\<alpha>,\<mu>) \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_prob_space (Y,\<beta>,\<nu>)) = distr (\<mu> \<Otimes>\<^sub>M \<nu>) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<beta>)"
  by(simp add: qbs_prob_pair_measure_computation distr_distr comp_assoc)

lemma qbs_prob_pair_measure_morphism:
 "case_prod qbs_prob_pair_measure \<in> monadP_qbs X \<Otimes>\<^sub>Q monadP_qbs Y \<rightarrow>\<^sub>Q monadP_qbs (X \<Otimes>\<^sub>Q Y)"
proof(rule pair_qbs_morphismI)
  fix \<beta>x \<beta>y
  assume h: "\<beta>x \<in> qbs_Mx (monadP_qbs X)" " \<beta>y \<in> qbs_Mx (monadP_qbs Y)"
  then obtain \<alpha>x \<alpha>y gx gy where ha:
   "\<alpha>x \<in> qbs_Mx X" "gx \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel" "\<beta>x = (\<lambda>r. qbs_prob_space (X, \<alpha>x, gx r))"
   "\<alpha>y \<in> qbs_Mx Y" "gy \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel" "\<beta>y = (\<lambda>r. qbs_prob_space (Y, \<alpha>y, gy r))"
    using rep_monadP_qbs_MPx[of \<beta>x X] rep_monadP_qbs_MPx[of \<beta>y Y] by auto
  note [measurable] = ha(2,5)
  have "(\<lambda>(x, y). x \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s y) \<circ> (\<lambda>r. (\<beta>x r, \<beta>y r)) = (\<lambda>r. qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha>x \<alpha>y \<circ> real_real.g, distr (gx r \<Otimes>\<^sub>M gy r) real_borel real_real.f))"
    apply standard
    using qbs_prob_MPx[OF ha(1,2)] qbs_prob_MPx[OF ha(4,5)] pair_qbs_probs.qbs_prob_pair_measure_computation[of X \<alpha>x _ Y \<alpha>y]
    by (auto simp: ha pair_qbs_probs_def)
  also have "... \<in> qbs_Mx (monadP_qbs (X \<Otimes>\<^sub>Q Y))"
    using qbs_prob_MPx[OF ha(1,2)] qbs_prob_MPx[OF ha(4,5)] pair_qbs_probs.ab_g_in_Mx[of X \<alpha>x _ Y \<alpha>y]
    by(auto intro!: bexI[where x="map_prod \<alpha>x \<alpha>y \<circ> real_real.g"] bexI[where x="\<lambda>r. distr (gx r \<Otimes>\<^sub>M gy r) real_borel real_real.f"]
         simp: monadP_qbs_MPx_def in_MPx_def pair_qbs_probs_def)
  finally show "(\<lambda>(x, y). x \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s y) \<circ> (\<lambda>r. (\<beta>x r, \<beta>y r)) \<in> qbs_Mx (monadP_qbs (X \<Otimes>\<^sub>Q Y))" .
qed

lemma(in pair_qbs_probs) qbs_prob_pair_measure_nnintegral:
  assumes "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "(\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(qbs_prob_space (X,\<alpha>,\<mu>) \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_prob_space (Y,\<beta>,\<nu>))) = (\<integral>\<^sup>+ z. (f \<circ> map_prod \<alpha> \<beta>) z \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
        (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+ x. ((f \<circ> map_prod \<alpha> \<beta>) \<circ> real_real.g) x \<partial>distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
    by(simp add: qbs_prob_ennintegral_def[OF assms] qbs_prob_pair_measure_computation)
  also have "... = (\<integral>\<^sup>+ x. ((f \<circ> map_prod \<alpha> \<beta>) \<circ> real_real.g) (real_real.f x) \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
    using assms by(intro nn_integral_distr) auto
  also have "... = ?rhs" by simp
  finally show ?thesis .
qed

lemma(in pair_qbs_probs) qbs_prob_pair_measure_integral:
  assumes "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    shows "(\<integral>\<^sub>Q z. f z \<partial>(qbs_prob_space (X,\<alpha>,\<mu>) \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_prob_space (Y,\<beta>,\<nu>))) = (\<integral>z. (f \<circ> map_prod \<alpha> \<beta>) z \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
          (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>x. ((f \<circ> map_prod \<alpha> \<beta>) \<circ> real_real.g) x \<partial>distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
    by(simp add: qbs_prob_integral_def[OF assms] qbs_prob_pair_measure_computation)
  also have "... = (\<integral> x. ((f \<circ> map_prod \<alpha> \<beta>) \<circ> real_real.g) (real_real.f x) \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
    using assms by(intro integral_distr) auto
  also have "... = ?rhs" by simp
  finally show ?thesis .
qed

lemma qbs_prob_pair_measure_eq_bind:
  assumes "p \<in> monadP_qbs_Px X"
      and "q \<in> monadP_qbs_Px Y"
    shows "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))"
proof -
  obtain \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  obtain \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_monadP_qbs_Px[OF assms(2)] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_probs_def hp hq)
  show ?thesis
    by(simp add: hp(1) hq(1) pqp.qbs_prob_pair_measure_computation(1) pqp.qbs_bind_return_pq(1))
qed

subsubsection \<open>Fubini Theorem\<close>
lemma qbs_prob_ennintegral_Fubini_fst:
  assumes "p \<in> monadP_qbs_Px X"
          "q \<in> monadP_qbs_Px Y"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. f (x,y) \<partial>q \<partial>p) = (\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
          (is "?lhs = ?rhs")
proof -
  note [simp] = qbs_bind_morphism[OF qbs_morphism_const[of _ "monadP_qbs Y",simplified,OF assms(2)] curry_preserves_morphisms[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]],simplified curry_def,simplified]
                qbs_morphism_Pair1'[OF _ qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]]
                assms(1)[simplified monadP_qbs_Px_def,simplified] assms(2)[simplified monadP_qbs_Px_def,simplified]
  have "?rhs = (\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))))"
    by(simp add: qbs_prob_pair_measure_eq_bind[OF assms(1,2)])
  also have "... = (\<integral>\<^sup>+\<^sub>Q x. qbs_prob_ennintegral (q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) f \<partial>p)"
    by(auto intro!: qbs_prob_ennintegral_bind[OF assms(1) _ assms(3)])
  also have "... =  (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. qbs_prob_ennintegral (qbs_return (X \<Otimes>\<^sub>Q Y) (x, y)) f \<partial>q \<partial>p)"
    by(auto intro!: qbs_prob_ennintegral_cong qbs_prob_ennintegral_bind[OF assms(2) _ assms(3)])
  also have "... = ?lhs"
    using assms(3) by(auto intro!: qbs_prob_ennintegral_cong qbs_prob_ennintegral_return)
  finally show ?thesis by simp
qed

lemma qbs_prob_ennintegral_Fubini_snd:
  assumes "p \<in> monadP_qbs_Px X"
          "q \<in> monadP_qbs_Px Y"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<integral>\<^sup>+\<^sub>Q y. \<integral>\<^sup>+\<^sub>Q x. f (x,y) \<partial>p \<partial>q) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
          (is "?lhs = ?rhs")
proof -
  note [simp] = qbs_bind_morphism[OF qbs_morphism_const[of _ "monadP_qbs X",simplified,OF assms(1)] curry_preserves_morphisms[OF qbs_morphism_pair_swap[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]],simplified curry_def,simplified]]
                qbs_morphism_Pair2'[OF _ qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]]
                assms(1)[simplified monadP_qbs_Px_def,simplified] assms(2)[simplified monadP_qbs_Px_def,simplified]
  have "?rhs = (\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))))"
    by(simp add: qbs_prob_pair_measure_eq_bind[OF assms(1,2)] qbs_bind_return_rotate[OF assms(1,2)])
  also have "... = (\<integral>\<^sup>+\<^sub>Q y. qbs_prob_ennintegral (p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) f \<partial>q)"
    by(auto intro!: qbs_prob_ennintegral_bind[OF assms(2) _ assms(3)])
  also have "... =  (\<integral>\<^sup>+\<^sub>Q y. \<integral>\<^sup>+\<^sub>Q x. qbs_prob_ennintegral (qbs_return (X \<Otimes>\<^sub>Q Y) (x, y)) f \<partial>p \<partial>q)"
    by(auto intro!: qbs_prob_ennintegral_cong qbs_prob_ennintegral_bind[OF assms(1) _ assms(3)])
  also have "... = ?lhs"
    using assms(3) by(auto intro!: qbs_prob_ennintegral_cong qbs_prob_ennintegral_return)
  finally show ?thesis by simp
qed

lemma qbs_prob_ennintegral_indep1:
  assumes "p \<in> monadP_qbs_Px X"
      and "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<integral>\<^sup>+\<^sub>Q z. f (fst z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>p)"
          (is "?lhs = _")
proof -
 obtain Y \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_prob_space[of q] by auto
  have "?lhs = (\<integral>\<^sup>+\<^sub>Q y. \<integral>\<^sup>+\<^sub>Q x. f x \<partial>p \<partial>q)"
    using qbs_prob_ennintegral_Fubini_snd[OF assms(1) qbs_prob.qbs_prob_space_in_Px[OF hq(2)] qbs_morphism_fst''[OF assms(2)]]
    by(simp add: hq(1))
  thus ?thesis
    by(simp add: qbs_prob_ennintegral_const)
qed

lemma qbs_prob_ennintegral_indep2:
  assumes "q \<in> monadP_qbs_Px Y"
      and "f \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<integral>\<^sup>+\<^sub>Q z. f (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sup>+\<^sub>Q y. f y \<partial>q)"
          (is "?lhs = _")
proof -
  obtain X \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of p] by auto
  have "?lhs = (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. f y \<partial>q \<partial>p)"
    using qbs_prob_ennintegral_Fubini_fst[OF qbs_prob.qbs_prob_space_in_Px[OF hp(2)] assms(1) qbs_morphism_snd''[OF assms(2)]]
    by(simp add: hp(1))
  thus ?thesis
    by(simp add: qbs_prob_ennintegral_const)
qed

lemma qbs_ennintegral_indep_mult:
  assumes "p \<in> monadP_qbs_Px X"
          "q \<in> monadP_qbs_Px Y"
          "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "g \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<integral>\<^sup>+\<^sub>Q z. f (fst z) * g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>p) * (\<integral>\<^sup>+\<^sub>Q y. g y \<partial>q)"
          (is "?lhs = ?rhs")
proof -
  have h:"(\<lambda>z. f (fst z) * g (snd z)) \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    using assms(4,3)
    by(auto intro!: borel_measurable_subalgebra[OF l_product_sets[of X Y]] simp: space_pair_measure lr_adjunction_correspondence)

  have "?lhs = (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y .f x * g y \<partial>q \<partial>p)"
    using qbs_prob_ennintegral_Fubini_fst[OF assms(1,2) h] by simp
  also have "... = (\<integral>\<^sup>+\<^sub>Q x. f x * \<integral>\<^sup>+\<^sub>Q y . g y \<partial>q \<partial>p)"
    using qbs_prob_ennintegral_cmult[of q,OF _ assms(4)] assms(2)
    by(simp add: monadP_qbs_Px_def)
  also have "... = ?rhs"
    using qbs_prob_ennintegral_cmult[of p,OF _ assms(3)] assms(1)
    by(simp add: ab_semigroup_mult_class.mult.commute[where b="qbs_prob_ennintegral q g"] monadP_qbs_Px_def)
  finally show ?thesis .
qed


lemma(in pair_qbs_probs) qbs_prob_pair_measure_integrable:
  assumes "qbs_integrable (qbs_prob_space (X,\<alpha>,\<mu>) \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_prob_space (Y,\<beta>,\<nu>)) f"
    shows "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
          "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (f \<circ> (map_prod \<alpha> \<beta>))"
proof -
  show "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using qbs_integrable_morphism[OF qbs_prob_pair_measure_qbs assms]
    by simp
next
  have 1:"integrable (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g))"
    using assms[simplified qbs_prob_pair_measure_computation] qbs_integrable_def[of f]
    by simp
  have "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>x. (f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g)) (real_real.f x))"
    by(intro integrable_distr[OF _ 1]) simp
  thus "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (f \<circ> map_prod \<alpha> \<beta>)"
    by(simp add: comp_def)
qed

lemma(in pair_qbs_probs) qbs_prob_pair_measure_integrable':
  assumes "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (f \<circ> (map_prod \<alpha> \<beta>))"
    shows "qbs_integrable (qbs_prob_space (X,\<alpha>,\<mu>) \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_prob_space (Y,\<beta>,\<nu>)) f"
proof -
  have "integrable (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) (f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g)) = integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>x. (f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g)) (real_real.f x))"
    by(intro integrable_distr_eq) (use assms(1) in auto)
  thus ?thesis
    using assms qbs_integrable_def
    by(simp add: comp_def qbs_prob_pair_measure_computation)
qed

lemma qbs_integrable_pair_swap:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  shows "qbs_integrable (q \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p) (\<lambda>(x,y). f (y,x))"
proof -
  obtain X \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of p] by auto
  obtain Y \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_prob_space[of q] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_probs_def hp hq)
  interpret pqp2: pair_qbs_probs Y \<beta> \<nu> X \<alpha> \<mu>
    by(simp add: pair_qbs_probs_def hp hq)

  have "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
       "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (f \<circ> map_prod \<alpha> \<beta>)"
    by(auto simp: pqp.qbs_prob_pair_measure_integrable[OF assms[simplified hp(1) hq(1)]])
  from qbs_morphism_pair_swap[OF this(1)] pqp.integrable_product_swap[OF this(2)]
  have "(\<lambda>(x,y). f (y,x)) \<in> Y \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
        "integrable (\<nu> \<Otimes>\<^sub>M \<mu>) ((\<lambda>(x,y). f (y,x)) \<circ> map_prod \<beta> \<alpha>)"
    by(simp_all add: map_prod_def comp_def split_beta')
  from pqp2.qbs_prob_pair_measure_integrable' [OF this]
  show ?thesis by(simp add: hp(1) hq(1))
qed

lemma qbs_integrable_pair1:
  assumes "p \<in> monadP_qbs_Px X"
          "q \<in> monadP_qbs_Px Y"
          "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
          "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. \<bar>f (x,y)\<bar> \<partial>q)"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> qbs_integrable q (\<lambda>y. f (x,y))"
    shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
proof -
  obtain \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  obtain \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_monadP_qbs_Px[OF assms(2)] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_probs_def hp hq)

  have "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (f \<circ> map_prod \<alpha> \<beta>)"
  proof(rule pqp.Fubini_integrable)
    show "f \<circ> map_prod \<alpha> \<beta> \<in> borel_measurable (\<mu> \<Otimes>\<^sub>M \<nu>)"
      using assms(3) by auto
  next
    have "(\<lambda>x. LINT y|\<nu>. norm ((f \<circ> map_prod \<alpha> \<beta>) (x, y))) = (\<lambda>x. \<integral>\<^sub>Q y. \<bar>f (x,y)\<bar> \<partial>q) \<circ> \<alpha>"
      apply standard subgoal for x
        using qbs_morphism_Pair1'[OF qbs_Mx_to_X(2)[OF pqp.qp1.in_Mx,of x] assms(3)]
        by(auto intro!: pqp.qp2.qbs_prob_integral_def[symmetric] simp: hq(1))
      done
    moreover have "integrable \<mu> ..."
      using assms(4) pqp.qp1.qbs_integrable_def
      by (simp add: hp(1))
    ultimately show "integrable \<mu> (\<lambda>x. LINT y|\<nu>. norm ((f \<circ> map_prod \<alpha> \<beta>) (x, y)))"
      by simp
  next
    have "\<And>x. integrable \<nu> (\<lambda>y. (f \<circ> map_prod \<alpha> \<beta>) (x, y))"
    proof-
      fix x
      have "(\<lambda>y. (f \<circ> map_prod \<alpha> \<beta>) (x, y)) = (\<lambda>y. f (\<alpha> x,y)) \<circ> \<beta>"
        by auto
      moreover have "qbs_integrable (qbs_prob_space (Y, \<beta>, \<nu>)) (\<lambda>y. f (\<alpha> x, y))"
        by(auto intro!: assms(5)[simplified hq(1)] simp: qbs_Mx_to_X)
      ultimately show "integrable \<nu> (\<lambda>y. (f \<circ> map_prod \<alpha> \<beta>) (x, y))"
        by(simp add: pqp.qp2.qbs_integrable_def)
    qed
    thus "AE x in \<mu>. integrable \<nu> (\<lambda>y. (f \<circ> map_prod \<alpha> \<beta>) (x, y))"
      by simp
  qed
  thus ?thesis
    using pqp.qbs_prob_pair_measure_integrable'[OF assms(3)]
    by(simp add: hp(1) hq(1))
qed

lemma qbs_integrable_pair2:
  assumes "p \<in> monadP_qbs_Px X"
          "q \<in> monadP_qbs_Px Y"
          "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
          "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. \<bar>f (x,y)\<bar> \<partial>p)"
      and "\<And>y. y \<in> qbs_space Y \<Longrightarrow> qbs_integrable p (\<lambda>x. f (x,y))"
    shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  using qbs_integrable_pair_swap[OF qbs_integrable_pair1[OF assms(2,1) qbs_morphism_pair_swap[OF assms(3)],simplified,OF assms(4,5)]]
  by simp

lemma qbs_integrable_fst:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  shows "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. f (x,y) \<partial>q)"
proof -
  obtain X \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of p] by auto
  obtain Y \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_prob_space[of q] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: hp hq  pair_qbs_probs_def)
  have h0: "p \<in> monadP_qbs_Px X" "q \<in> monadP_qbs_Px Y" "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using qbs_integrable_morphism[OF _ assms,simplified qbs_prob_pair_measure_qbs]
    by(simp_all add: monadP_qbs_Px_def hp(1) hq(1))

  show "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q)"
  proof(auto simp add: pqp.qp1.qbs_integrable_def hp(1))
    show "(\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<in> borel_measurable (qbs_to_measure X)"
      using qbs_morphism_integral_fst[OF h0(2,3)] by auto
  next
    have "integrable \<mu> (\<lambda>x. LINT y|\<nu>. (f \<circ> map_prod \<alpha> \<beta>) (x, y))"
      by(intro pqp.integrable_fst') (rule pqp.qbs_prob_pair_measure_integrable(2)[OF assms[simplified hp(1) hq(1)]])
    moreover have "\<And>x. ((\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<circ> \<alpha>) x = LINT y|\<nu>. (f \<circ> map_prod \<alpha> \<beta>) (x, y)"
     by(auto intro!: pqp.qp2.qbs_prob_integral_def qbs_morphism_Pair1'[OF qbs_Mx_to_X(2)[OF pqp.qp1.in_Mx] h0(3)] simp: hq)
    ultimately show "integrable \<mu> ((\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<circ> \<alpha>)"
      using Bochner_Integration.integrable_cong[of \<mu> \<mu> "(\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<circ> \<alpha>" " (\<lambda>x. LINT y|\<nu>. (f \<circ> map_prod \<alpha> \<beta>) (x, y))"]
      by simp
  qed
qed

lemma qbs_integrable_snd:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  shows "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. f (x,y) \<partial>p)"
  using qbs_integrable_fst[OF qbs_integrable_pair_swap[OF assms]]
  by simp

lemma qbs_integrable_indep_mult:
  assumes "qbs_integrable p f"
      and "qbs_integrable q g"
    shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. f (fst x) * g (snd x))"
proof -
  obtain X \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of p] by auto
  obtain Y \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_prob_space[of q] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: hp hq  pair_qbs_probs_def)
  have h0: "p \<in> monadP_qbs_Px X" "q \<in> monadP_qbs_Px Y" "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" "g \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using qbs_integrable_morphism[OF _ assms(1)] qbs_integrable_morphism[OF _ assms(2)]
    by(simp_all add: monadP_qbs_Px_def hp(1) hq(1))

  show ?thesis
  proof(rule qbs_integrable_pair1[OF h0(1,2)],simp_all add: assms(2))
    show "(\<lambda>z. f (fst z) * g (snd z)) \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      using h0(3,4) by(auto intro!: borel_measurable_subalgebra[OF l_product_sets[of X Y]] simp: space_pair_measure lr_adjunction_correspondence)
  next
    show "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. \<bar>f x * g y\<bar> \<partial>q)"
      by(auto intro!: qbs_integrable_mult[OF qbs_integrable_abs[OF assms(1)]]
           simp only: idom_abs_sgn_class.abs_mult qbs_prob_integral_cmult ab_semigroup_mult_class.mult.commute[where b="\<integral>\<^sub>Q y. \<bar>g y\<bar> \<partial>q"])
  qed
qed

lemma qbs_integrable_indep1:
  assumes "qbs_integrable p f"
  shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. f (fst x))"
  using qbs_integrable_indep_mult[OF assms qbs_integrable_const[of q 1]]
  by simp

lemma qbs_integrable_indep2:
  assumes "qbs_integrable q g"
  shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. g (snd x))"
  using qbs_integrable_pair_swap[OF qbs_integrable_indep1[OF assms],of p]
  by(simp add: split_beta')


lemma qbs_prob_integral_Fubini_fst:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
    shows "(\<integral>\<^sub>Q x. \<integral>\<^sub>Q y. f (x,y) \<partial>q \<partial>p) = (\<integral>\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
          (is "?lhs = ?rhs")
proof -
  obtain X \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of p] by auto
  obtain Y \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_prob_space[of q] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: hp hq  pair_qbs_probs_def)
  have h0: "p \<in> monadP_qbs_Px X" "q \<in> monadP_qbs_Px Y" "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using qbs_integrable_morphism[OF _ assms,simplified qbs_prob_pair_measure_qbs]
    by(simp_all add: monadP_qbs_Px_def hp(1) hq(1))

  have "?lhs = (\<integral> x. \<integral>\<^sub>Q y. f (\<alpha> x, y) \<partial>q \<partial>\<mu>)"
    using qbs_morphism_integral_fst[OF h0(2) h0(3)]
    by(auto intro!: pqp.qp1.qbs_prob_integral_def simp: hp(1))
  also have "... = (\<integral>x. \<integral>y. f (\<alpha> x, \<beta> y) \<partial>\<nu> \<partial>\<mu>)"
    using qbs_morphism_Pair1'[OF qbs_Mx_to_X(2)[OF pqp.qp1.in_Mx] h0(3)]
    by(auto intro!: Bochner_Integration.integral_cong pqp.qp2.qbs_prob_integral_def
              simp: hq(1))
  also have "... = (\<integral>z. (f \<circ> map_prod \<alpha> \<beta>) z \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
    using pqp.integral_fst'[OF pqp.qbs_prob_pair_measure_integrable(2)[OF assms[simplified hp(1) hq(1)]]]
    by(simp add: map_prod_def comp_def)
  also have "... = ?rhs"
    by(simp add: pqp.qbs_prob_pair_measure_integral[OF h0(3)] hp(1) hq(1))
  finally show ?thesis .
qed

lemma qbs_prob_integral_Fubini_snd:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
    shows "(\<integral>\<^sub>Q y. \<integral>\<^sub>Q x. f (x,y) \<partial>p \<partial>q) = (\<integral>\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
          (is "?lhs = ?rhs")
proof -
  obtain X \<alpha> \<mu> where hp:
    "p = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of p] by auto
  obtain Y \<beta> \<nu> where hq:
   "q = qbs_prob_space (Y, \<beta>, \<nu>)" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_prob_space[of q] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: hp hq  pair_qbs_probs_def)
  have h0: "p \<in> monadP_qbs_Px X" "q \<in> monadP_qbs_Px Y" "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using qbs_integrable_morphism[OF _ assms,simplified qbs_prob_pair_measure_qbs]
    by(simp_all add: monadP_qbs_Px_def hp(1) hq(1))

  have "?lhs = (\<integral> y. \<integral>\<^sub>Q x. f (x,\<beta> y) \<partial>p \<partial>\<nu>)"
    using qbs_morphism_integral_snd[OF h0(1) h0(3)]
    by(auto intro!: pqp.qp2.qbs_prob_integral_def simp: hq(1))
  also have "... = (\<integral>y. \<integral>x. f (\<alpha> x, \<beta> y) \<partial>\<mu> \<partial>\<nu>)"
    using qbs_morphism_Pair2'[OF qbs_Mx_to_X(2)[OF pqp.qp2.in_Mx] h0(3)]
    by(auto intro!: Bochner_Integration.integral_cong pqp.qp1.qbs_prob_integral_def
              simp: hp(1))
  also have "... = (\<integral>z. (f \<circ> map_prod \<alpha> \<beta>) z \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
    using pqp.integral_snd[of "curry (f \<circ> map_prod \<alpha> \<beta>)"] pqp.qbs_prob_pair_measure_integrable(2)[OF assms[simplified hp(1) hq(1)]]
    by(simp add: map_prod_def comp_def split_beta')
  also have "... = ?rhs"
    by(simp add: pqp.qbs_prob_pair_measure_integral[OF h0(3)] hp(1) hq(1))
  finally show ?thesis .
qed

lemma qbs_prob_integral_indep1:
  assumes "qbs_integrable p f"
  shows "(\<integral>\<^sub>Q z. f (fst z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q x. f x \<partial>p)"
  using qbs_prob_integral_Fubini_snd[OF qbs_integrable_indep1[OF assms],of q]
  by(simp add: qbs_prob_integral_const)

lemma qbs_prob_integral_indep2:
  assumes "qbs_integrable q g"
  shows "(\<integral>\<^sub>Q z. g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q y. g y \<partial>q)"
  using qbs_prob_integral_Fubini_fst[OF qbs_integrable_indep2[OF assms],of p]
  by(simp add: qbs_prob_integral_const)

lemma qbs_prob_integral_indep_mult:
  assumes "qbs_integrable p f"
      and "qbs_integrable q g"
    shows "(\<integral>\<^sub>Q z. f (fst z) * g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q x. f x \<partial>p) * (\<integral>\<^sub>Q y. g y \<partial>q)"
          (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sub>Q x. \<integral>\<^sub>Q y. f x * g y \<partial>q \<partial>p)"
    using qbs_prob_integral_Fubini_fst[OF qbs_integrable_indep_mult[OF assms]]
    by simp
  also have "... = (\<integral>\<^sub>Q x. f x * (\<integral>\<^sub>Q y.  g y \<partial>q) \<partial>p)"
    by(simp add: qbs_prob_integral_cmult)
  also have "... = ?rhs"
    by(simp add: qbs_prob_integral_cmult ab_semigroup_mult_class.mult.commute[where b="\<integral>\<^sub>Q y.  g y \<partial>q"])
  finally show ?thesis .
qed

lemma qbs_prob_var_indep_plus:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
          "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>z. (f z)\<^sup>2)"
          "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"
          "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>z. (g z)\<^sup>2)"
          "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>z. (f z) * (g z))"
      and "(\<integral>\<^sub>Q z. f z * g z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) * (\<integral>\<^sub>Q z. g z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
    shows "qbs_prob_var (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>z. f z + g z) = qbs_prob_var (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f + qbs_prob_var (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"
  unfolding qbs_prob_var_def
proof -
  show "(\<integral>\<^sub>Q z. (f z + g z - \<integral>\<^sub>Q w. f w + g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))\<^sup>2 \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q z. (f z - qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f)\<^sup>2 \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) + (\<integral>\<^sub>Q z. (g z - qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g)\<^sup>2 \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
       (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sub>Q z. ((f z - (\<integral>\<^sub>Q w. f w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))) + (g z - (\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))))\<^sup>2 \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
      by(simp add: qbs_prob_integral_add[OF assms(1,3)] add_diff_add)
    also have "... = (\<integral>\<^sub>Q z. (f z - (\<integral>\<^sub>Q w. f w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)))\<^sup>2 + (g z - (\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)))\<^sup>2 + (2 * f z * g z - 2 * (\<integral>\<^sub>Q w. f w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) * g z - (2 * f z * (\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) - 2 * (\<integral>\<^sub>Q w. f w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) * (\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)))) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
      by(simp add: comm_semiring_1_class.power2_sum comm_semiring_1_cancel_class.left_diff_distrib' ring_class.right_diff_distrib)
    also have "... = ?rhs"
      using qbs_prob_integral_add[OF qbs_integrable_add[OF qbs_integrable_sq[OF assms(1,2)] qbs_integrable_sq[OF assms(3,4)]] qbs_integrable_diff[OF qbs_integrable_diff[OF qbs_integrable_mult[OF assms(5),of 2,simplified comm_semiring_1_class.semiring_normalization_rules(18)] qbs_integrable_mult[OF assms(3),of "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"]] qbs_integrable_diff[OF qbs_integrable_mult[OF assms(1),of "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g",simplified ab_semigroup_mult_class.mult_ac(1)[where b="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] ab_semigroup_mult_class.mult.commute[where a="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] comm_semiring_1_class.semiring_normalization_rules(18)[of _ _ "qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]] qbs_integrable_const[of _ "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]]]]
            qbs_prob_integral_add[OF qbs_integrable_sq[OF assms(1,2)] qbs_integrable_sq[OF assms(3,4)]]
            qbs_prob_integral_diff[OF qbs_integrable_diff[OF qbs_integrable_mult[OF assms(5),of 2,simplified comm_semiring_1_class.semiring_normalization_rules(18)] qbs_integrable_mult[OF assms(3),of "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"]] qbs_integrable_diff[OF qbs_integrable_mult[OF assms(1),of "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g",simplified ab_semigroup_mult_class.mult_ac(1)[where b="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] ab_semigroup_mult_class.mult.commute[where a="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] comm_semiring_1_class.semiring_normalization_rules(18)[of _ _ "qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]] qbs_integrable_const[of _ "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]]]
            qbs_prob_integral_diff[OF qbs_integrable_mult[OF assms(5),of 2,simplified comm_semiring_1_class.semiring_normalization_rules(18)] qbs_integrable_mult[OF assms(3),of "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"]]
            qbs_prob_integral_diff[OF qbs_integrable_mult[OF assms(1),of "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g",simplified ab_semigroup_mult_class.mult_ac(1)[where b="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] ab_semigroup_mult_class.mult.commute[where a="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] comm_semiring_1_class.semiring_normalization_rules(18)[of _ _ "qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]] qbs_integrable_const[of _ "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]]
            qbs_prob_integral_cmult[of "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q" 2 "\<lambda>z. f z * g z",simplified assms(6) comm_semiring_1_class.semiring_normalization_rules(18)]
            qbs_prob_integral_cmult[of "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q" "2 * (\<integral>\<^sub>Q w. f w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" g]
            qbs_prob_integral_cmult[of "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q" "2 * (\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" f,simplified semigroup_mult_class.mult.assoc[of 2 "\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)"] ab_semigroup_mult_class.mult.commute[where a="qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"] comm_semiring_1_class.semiring_normalization_rules(18)[of 2 _ "\<integral>\<^sub>Q w. g w \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)"]]
            qbs_prob_integral_const[of "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q" "2 * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f * qbs_prob_integral (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) g"]
      by simp
    finally show ?thesis .
  qed
qed

lemma qbs_prob_var_indep_plus':
  assumes "qbs_integrable p f"
          "qbs_integrable p (\<lambda>x. (f x)\<^sup>2)"
          "qbs_integrable q g"
      and "qbs_integrable q (\<lambda>x. (g x)\<^sup>2)"
    shows "qbs_prob_var (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>z. f (fst z) + g (snd z)) = qbs_prob_var p f + qbs_prob_var q g"
  using qbs_prob_var_indep_plus[OF qbs_integrable_indep1[OF assms(1)] qbs_integrable_indep1[OF assms(2)] qbs_integrable_indep2[OF assms(3)] qbs_integrable_indep2[OF assms(4)] qbs_integrable_indep_mult[OF assms(1) assms(3)] qbs_prob_integral_indep_mult[OF assms(1) assms(3),simplified  qbs_prob_integral_indep1[OF assms(1),of q,symmetric] qbs_prob_integral_indep2[OF assms(3),of p,symmetric]]]
        qbs_prob_integral_indep1[OF qbs_integrable_sq[OF assms(1,2)],of q "\<integral>\<^sub>Q z. f (fst z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)"] qbs_prob_integral_indep2[OF qbs_integrable_sq[OF assms(3,4)],of p "\<integral>\<^sub>Q z. g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)"]
  by(simp add: qbs_prob_var_def qbs_prob_integral_indep1[OF assms(1)] qbs_prob_integral_indep2[OF assms(3)])

end
